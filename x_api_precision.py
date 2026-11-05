#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Precision X API supplement for the repaired webarchived_tweet_downloader.

Standalone: python x_api_precision.py TARGET --precision-ids ID --precision-mode 1
Patched entry: python download_archive.py TARGET --precision-ids ID --precision-mode 1

The existing download_archive.py is imported as a library, never rewritten here.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import deque
from copy import deepcopy
from datetime import datetime, timedelta, timezone
from dataclasses import replace
from hashlib import sha256
import json
import logging
import os
from pathlib import Path
import re
import sys
import tempfile
from time import gmtime
from uuid import uuid4
from typing import Any, Optional

import download_archive as core

USER_RE = re.compile(r"^[A-Za-z0-9_]{1,15}$")
ID_RE = re.compile(r"^(?:https?://(?:www\.)?(?:twitter\.com|x\.com)/[^/]+/status/)?([0-9]{5,25})(?:[/?#].*)?$", re.I)
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


class PrecisionError(RuntimeError):
    pass


# Log messages include tweet IDs / errors / file paths, never API tokens or
# full API response bodies. Unexpected exception tracebacks are redacted too.
_SECRET_PATTERNS = (
    re.compile(r'(?i)\b(Bearer\s+)[A-Za-z0-9._~+/-]+'),
    re.compile(r'(?i)\b((?:X_BEARER_TOKEN|BEARER_TOKEN|API_KEY|API_SECRET|ACCESS_TOKEN|authorization)\s*[:=]\s*)[^\s,;]+'),
    re.compile(r'(?i)([?&](?:access_token|api_key|bearer_token|client_secret)=)[^&\s]+'),
)


def redact_log(text: str) -> str:
    result = str(text)
    for pattern in _SECRET_PATTERNS:
        result = pattern.sub(lambda match: match.group(1) + '[REDACTED]', result)
    return result


class _SafeFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        return redact_log(super().format(record))


class RunDiagnostics:
    """Per-run append-only audit + warning/error logs; no archive JSON edits."""

    def __init__(self, asset_dir: Path, target: str):
        self.directory = Path(asset_dir) / 'precision_logs'
        self.directory.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S_%f')
        basename = f'precision_{stamp}_{os.getpid()}_{uuid4().hex[:8]}'
        self.run_path = self.directory / (basename + '.log')
        self.error_path = self.directory / (basename + '.errors.log')
        self.logger = logging.getLogger('precision-' + basename)
        self.logger.setLevel(logging.DEBUG)
        self.logger.propagate = False
        formatter = _SafeFormatter('%(asctime)s UTC [%(levelname)s] %(message)s',
                                   datefmt='%Y-%m-%d %H:%M:%S')
        formatter.converter = gmtime
        self.handlers = []
        try:
            for path, level in ((self.run_path, logging.DEBUG),
                                (self.error_path, logging.WARNING)):
                handler = logging.FileHandler(path, mode='x', encoding='utf-8')
                handler.setLevel(level)
                handler.setFormatter(formatter)
                self.logger.addHandler(handler)
                self.handlers.append(handler)
        except Exception:
            self.close()
            raise
        self.logger.info('Precision run started. Archive target: @%s. Logs created outside JSON/media directories.', target)

    def close(self) -> None:
        for handler in getattr(self, 'handlers', []):
            handler.flush()
            handler.close()
            self.logger.removeHandler(handler)
        self.handlers = []


class LoggedIssues(list):
    """Preserve legacy list behavior while writing each warning immediately."""

    def __init__(self, callback):
        super().__init__()
        self.callback = callback

    def append(self, issue):
        super().append(issue)
        self.callback(str(issue))


def clean_user(value: str) -> str:
    user = value.strip().lstrip('@')
    if not USER_RE.fullmatch(user):
        raise PrecisionError(f"Invalid Twitter/X username: {value!r}")
    return user


def clean_id(value: str) -> str:
    match = ID_RE.fullmatch(value.strip())
    if not match:
        raise PrecisionError(f"Invalid tweet ID or status URL: {value!r}")
    return match.group(1)


def parse_date_arg(text: str, *, is_end: bool = False) -> str:
    """Date-only end is inclusive; datetime end is exclusive. Both UTC."""
    raw = text.strip()
    if DATE_RE.fullmatch(raw):
        dt = datetime.strptime(raw, "%Y-%m-%d").replace(tzinfo=timezone.utc)
        if is_end:
            dt += timedelta(days=1)
    else:
        try:
            dt = datetime.fromisoformat(raw.replace('Z', '+00:00'))
        except ValueError as exc:
            raise PrecisionError(f"Bad ISO date/time: {raw!r}") from exc
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        dt = dt.astimezone(timezone.utc)
    return dt.strftime('%Y-%m-%dT%H:%M:%SZ')


def primary_node(payload: dict, tweet_id: str) -> Optional[dict]:
    if not isinstance(payload, dict):
        return None
    item = payload.get('data')
    if isinstance(item, dict) and str(item.get('id', '')) == tweet_id and core._is_extractable_tweet_node(item):
        return item
    return core.find_tweet_node_by_id(payload, tweet_id)


def reply_parent(node: dict) -> str:
    if not isinstance(node, dict):
        return ''
    return core._extract_metadata_from_node(node).get('in_reply_to_status_id', '')


def primary_time(node: dict, fallback: str = '') -> datetime:
    raw = core._tweet_node_created_at(node)
    dt = core._parse_tweet_created_at(raw)
    if dt is not None:
        return dt
    if fallback and re.fullmatch(r'\d{14}', fallback):
        return datetime.strptime(fallback, '%Y%m%d%H%M%S')
    raise PrecisionError('Cannot establish publication time; refusing to invent a timestamp.')


def author_identity(payload: dict, node: dict) -> tuple[str, str, dict]:
    name, _display = core._extract_user_info(payload, node)
    legacy = node.get('legacy', {}) if isinstance(node.get('legacy'), dict) else {}
    uid = str(node.get('author_id') or node.get('user_id_str') or legacy.get('user_id_str') or '')
    users = payload.get('includes', {}).get('users', []) if isinstance(payload.get('includes'), dict) else []
    for user in users or []:
        if isinstance(user, dict) and (not uid or str(user.get('id')) == uid):
            if str(user.get('id', '')) == uid or (not uid and user.get('username', '').casefold() == name.casefold()):
                uid = uid or str(user.get('id', ''))
                return (name or str(user.get('username', '')), uid, deepcopy(user))
    # Wayback legacy user profile, if present.
    core_info = node.get('core', {}) if isinstance(node.get('core'), dict) else {}
    user_results = core_info.get('user_results', {}) if isinstance(core_info.get('user_results'), dict) else {}
    result = user_results.get('result', {}) if isinstance(user_results.get('result'), dict) else {}
    if not uid:
        uid = str(result.get('rest_id') or result.get('id_str') or '')
    user_legacy = result.get('legacy', {}) if isinstance(result.get('legacy'), dict) else {}
    flat_user = node.get('user', {}) if isinstance(node.get('user'), dict) else {}
    if not user_legacy:
        user_legacy = flat_user
    if not uid:
        uid = str(user_legacy.get('id_str') or user_legacy.get('id') or '')
    profile = {'id': uid, 'username': name or user_legacy.get('screen_name', ''), 'name': user_legacy.get('name', '')}
    key_map = {
        'description': 'description', 'location': 'location', 'url': 'url',
        'profile_image_url_https': 'profile_image_url', 'profile_image_url': 'profile_image_url',
        'created_at': 'created_at', 'protected': 'protected', 'verified': 'verified',
        'entities': 'entities',
    }
    for old, new in key_map.items():
        if old in user_legacy:
            profile[new] = deepcopy(user_legacy[old])
    if 'followers_count' in user_legacy or 'friends_count' in user_legacy:
        profile['public_metrics'] = {
            'followers_count': user_legacy.get('followers_count', 0),
            'following_count': user_legacy.get('friends_count', 0),
            'tweet_count': user_legacy.get('statuses_count', 0),
            'listed_count': user_legacy.get('listed_count', 0),
        }
    return name or str(profile.get('username', '')), uid, profile


class LocalArchive:
    """Index only main JSON snapshots; never modifies existing snapshot JSON."""

    def __init__(self, json_dir: Path, target_user: str):
        self.json_dir = json_dir
        self.target = target_user.casefold()
        self.main_files: dict[str, Path] = {}
        self.valid_payloads: dict[str, dict] = {}
        self.reply_cache_payloads: dict[str, dict] = {}
        self.history: list[tuple[datetime, str, dict]] = []
        self.occupied: set[str] = set()
        self._scan()

    def _scan(self) -> None:
        if not self.json_dir.is_dir():
            return
        for path in sorted(self.json_dir.glob('*.json')):
            parsed = core.parse_snapshot_filename(path.name)
            if not parsed:
                continue
            ts, tid = parsed
            self.occupied.add(tid)
            data = core.load_snapshot_json(path)
            # The original downloader stores resolved ancestors under
            # _pale_fire.x_api_reply_chains, not necessarily as separate JSON.
            # Index these locally before considering paid lookups.
            if isinstance(data, dict):
                cache = data.get(core.X_API_JSON_CACHE_KEY, {})
                chains = cache.get(core.X_API_REPLY_CHAINS_KEY, {}) if isinstance(cache, dict) else {}
                if isinstance(chains, dict):
                    for entry in chains.values():
                        if not isinstance(entry, dict):
                            continue
                        for item in entry.get('posts', []) or []:
                            if not isinstance(item, dict):
                                continue
                            cached_id = str(item.get('id') or '')
                            cached_payload = item.get('payload')
                            if cached_id and isinstance(cached_payload, dict) and primary_node(cached_payload, cached_id):
                                self.reply_cache_payloads.setdefault(cached_id, cached_payload)
            node = primary_node(data, tid) if isinstance(data, dict) else None
            if not node:
                continue
            if tid in self.main_files:
                continue
            self.main_files[tid] = path
            self.valid_payloads[tid] = data
            name, uid, profile = author_identity(data, node)
            if name.casefold() != self.target:
                continue
            try:
                dt = primary_time(node, ts)
            except PrecisionError:
                continue
            if profile.get('username'):
                self.history.append((dt, uid, profile))
        self.history.sort(key=lambda item: item[0])

    def get(self, tid: str) -> Optional[dict]:
        data = self.valid_payloads.get(tid)
        if data is not None:
            return data
        if tid in self.reply_cache_payloads:
            return self.reply_cache_payloads[tid]
        # Embedded tweets in another valid archive may provide a useful parent.
        if self.json_dir.exists():
            return core.find_local_snapshot_payload_for_tweet(tid, self.json_dir)
        return None

    def existing_main(self, tid: str) -> bool:
        return tid in self.main_files

    def historical_user(self, dt: datetime, target_id: str = '') -> Optional[dict]:
        if not self.history:
            return None
        # Prefer correct account ID, when the old archive exposes it.
        candidates = [(date, user) for date, uid, user in self.history if not (target_id and uid and uid != target_id)]
        if not candidates:
            return None
        dates = [entry[0] for entry in candidates]
        idx = bisect_right(dates, dt)
        return deepcopy(candidates[idx - 1 if idx else 0][1])

    def add(self, tid: str, path: Path, payload: dict) -> None:
        self.main_files[tid] = path
        self.valid_payloads[tid] = payload
        self.occupied.add(tid)


def slim_includes(tweet: dict, includes: dict) -> dict:
    """Keep the target post's own expansions AND its direct quote/repost expansions.

    Search results include expanded quoted/retweeted posts. Removing their
    authors or media entries can break offline quote/repost rendering, even
    when the seed tweet itself was saved correctly. This never issues API calls.
    """
    if not isinstance(includes, dict):
        return {}

    references = [ref for ref in tweet.get('referenced_tweets', []) or []
                  if isinstance(ref, dict)]
    ref_ids = {str(ref.get('id')) for ref in references if ref.get('id')}
    expanded_tweets = [x for x in includes.get('tweets', []) or []
                       if isinstance(x, dict) and str(x.get('id')) in ref_ids]

    relevant_posts = [tweet, *expanded_tweets]
    user_ids: set[str] = set()
    media_keys: set[str] = set()
    for post in relevant_posts:
        for field in ('author_id', 'in_reply_to_user_id'):
            if post.get(field):
                user_ids.add(str(post[field]))
        attachments = post.get('attachments')
        if isinstance(attachments, dict):
            media_keys.update(str(key) for key in attachments.get('media_keys', []) or [])
    for ref in references:
        if ref.get('author_id'):
            user_ids.add(str(ref['author_id']))

    result = {}
    for key, items in includes.items():
        if not isinstance(items, list):
            continue
        if key == 'users':
            result[key] = [deepcopy(x) for x in items
                           if isinstance(x, dict) and str(x.get('id', '')) in user_ids]
        elif key == 'media':
            result[key] = [deepcopy(x) for x in items
                           if isinstance(x, dict) and str(x.get('media_key', '')) in media_keys]
        elif key == 'tweets':
            result[key] = deepcopy(expanded_tweets)
        elif key == 'polls':
            result[key] = deepcopy(items)
    return result


class PrecisionJob:
    def __init__(self, *, target: str, mode: int, api_username: str = '', newname: bool = False,
                 json_only: bool = False, x_api_only: bool = False, env_files: list[str],
                 diagnostics: Optional[RunDiagnostics] = None):
        self.target = target
        self.diagnostics = diagnostics
        self.mode = mode
        self.api_username = api_username
        self.newname = newname
        self.json_only = json_only
        self.x_api_only = x_api_only
        self.output_path, self.asset_dir, _, self.json_dir, _ = core.build_output_paths(target)
        self.local = LocalArchive(self.json_dir, target)
        self.auths = self._credentials(env_files)
        self.search_cache: dict[tuple[str, str, str], list[tuple[dict, dict]]] = {}
        self.cache_dir = self.asset_dir / "precision_api_cache"
        self.api_cache: dict[str, tuple[dict, str]] = {}
        self.resolved_cache: dict[str, tuple[dict, str]] = {}
        self.children_done: set[str] = set()
        self.written_records: list = []
        self.seen_new_ids: set[str] = set()
        self.target_author_ids: set[str] = set()
        # Mode-2 ID lookups with a locally archived root use THAT root's
        # profile for newly fetched descendants, not a different dated post.
        self.pinned_root_profiles: dict[str, dict] = {}
        self.request_count = 0
        self.skipped = 0
        self.errors: list[str] = LoggedIssues(self._log_issue)
        self.new_ids: set[str] = set()
        if self.newname and not self.local.history:
            raise PrecisionError('NewName requires existing valid local JSON by the target user for historical profile lookup. No API call made.')
        if not self.auths:
            raise PrecisionError('No X API credentials found; check the .env file. No API call made.')

    def _event(self, level: str, message: str, *args, exc_info: bool = False) -> None:
        diagnostics = getattr(self, 'diagnostics', None)
        if diagnostics is not None:
            getattr(diagnostics.logger, level)(message, *args, exc_info=exc_info)

    def _log_issue(self, message: str) -> None:
        self._event('warning', 'ISSUE: %s', message)

    @staticmethod
    def _credentials(files: list[str]):
        for filename in files:
            core.load_env_file(Path(filename))
        auths = core.get_x_api_auths_from_env_files(files, 'X_BEARER_TOKEN')
        if not auths:
            fallback = core.get_x_api_auth('X_BEARER_TOKEN')
            if fallback:
                auths = [fallback]
        return auths

    def _cache_expanded_tweets(self, includes: dict, source: str) -> None:
        """Reuse expanded quote/repost/reply posts already returned by paid API."""
        if not isinstance(includes, dict):
            return
        for post in includes.get('tweets', []) or []:
            if not isinstance(post, dict):
                continue
            tid = str(post.get('id') or '')
            # Expanded objects without timestamps are not suitable standalone
            # snapshots; let local/Wayback lookup resolve them instead.
            if not tid or not post.get('created_at') or not primary_node({'data': post}, tid):
                continue
            payload = {'data': deepcopy(post), 'includes': slim_includes(post, includes)}
            self.api_cache.setdefault(tid, (payload, source + ':expanded'))

    def _request_search(self, query: str, start: str = '', end: str = '') -> list[tuple[dict, dict]]:
        """Paged full-archive search with atomic on-disk checkpoints.

        Cached results are reused only briefly, to avoid permanently missing new
        replies from stale search results. Interrupted searches can resume from
        the last safely written page instead of paying for those pages again.
        """
        key = (query, start, end)
        if key in self.search_cache:
            self._event('debug', 'SEARCH cache hit: query=%r start=%s end=%s', query, start, end)
            return self.search_cache[key]
        digest = sha256(json.dumps(key, ensure_ascii=False).encode('utf-8')).hexdigest()
        checkpoint_path = self.cache_dir / (digest + '.json')
        state = {'version': 1, 'query': query, 'start': start, 'end': end,
                 'pages': [], 'next_token': '', 'complete': False}
        if checkpoint_path.is_file():
            self._event('info', 'SEARCH checkpoint found: %s', checkpoint_path)
            try:
                loaded = json.loads(checkpoint_path.read_text(encoding='utf-8'))
                saved_at = datetime.fromisoformat(str(loaded.get('saved_at', '')).replace('Z', '+00:00'))
                age = datetime.now(timezone.utc) - saved_at
                if (isinstance(loaded, dict) and loaded.get('version') == 1
                        and (loaded.get('query'), loaded.get('start'), loaded.get('end')) == key
                        and isinstance(loaded.get('pages'), list)
                        and timedelta(0) <= age <= timedelta(hours=24)):
                    state = loaded
                    self._event('info', 'SEARCH checkpoint resumed: query=%r saved_pages=%d complete=%s',
                                query, len(state['pages']), state['complete'])
            except (OSError, ValueError, TypeError, AttributeError) as exc:
                self._event('warning', 'SEARCH checkpoint unreadable: path=%s error=%s', checkpoint_path, exc)
        collected: list[tuple[dict, dict]] = []
        seen_tokens: set[str] = set()

        def accept_page(payload: dict, source: str) -> str:
            meta = payload.get('meta')
            if not isinstance(meta, dict):
                raise PrecisionError(f'X API search response missing pagination metadata for {query!r}.')
            page = payload.get('data', [])
            if not isinstance(page, list):
                raise PrecisionError(f'X API search response contains invalid post data for {query!r}.')
            count = meta.get('result_count')
            if count is not None and (not isinstance(count, int) or count != len(page)):
                raise PrecisionError(f'X API search returned an inconsistent result count for {query!r}.')
            if payload.get('errors'):
                detail = core.format_api_error_payload(payload) or str(payload['errors'])
                if not page:
                    raise PrecisionError(f'X API search returned errors and no posts for {query!r}: {detail}')
                self.errors.append(f'X API search {query!r} returned partial expansion errors: {detail}')
            self._cache_expanded_tweets(payload.get('includes', {}), source)
            for post in page:
                if not isinstance(post, dict) or not post.get('id'):
                    raise PrecisionError(f'X API search contains a post without a valid ID: {query!r}.')
                includes = slim_includes(post, payload.get('includes', {}))
                collected.append((deepcopy(post), includes))
                self.api_cache.setdefault(str(post['id']),
                                          ({'data': deepcopy(post), 'includes': deepcopy(includes)}, source))
            return str(meta.get('next_token') or '')

        for saved in state['pages']:
            if not isinstance(saved, dict) or not isinstance(saved.get('payload'), dict):
                raise PrecisionError(f'Corrupt paid-search checkpoint {checkpoint_path}; refusing to use it.')
            token = accept_page(saved['payload'], str(saved.get('source') or 'x_api_checkpoint'))
            if token:
                if token in seen_tokens:
                    raise PrecisionError('Repeated token in search checkpoint.')
                seen_tokens.add(token)
        if state['complete']:
            self._event('info', 'SEARCH complete checkpoint reused: query=%r pages=%d posts=%d; no paid requests',
                        query, len(state['pages']), len(collected))
            self.search_cache[key] = collected
            return collected
        next_token = str(state.get('next_token') or '')
        if state['pages'] and not next_token:
            raise PrecisionError('Incomplete search checkpoint has no continuation token; cannot safely resume.')
        while True:
            params = {
                'query': query, 'max_results': '500',
                'tweet.fields': core.X_API_TWEET_FIELDS,
                'expansions': core.X_API_EXPANSIONS,
                'user.fields': core.X_API_USER_FIELDS,
                'media.fields': core.X_API_MEDIA_FIELDS,
            }
            if start:
                params['start_time'] = start
            if end:
                params['end_time'] = end
            if next_token:
                params['next_token'] = next_token
            self.request_count += 1
            self._event('info', 'SEARCH API request: query=%r start=%s end=%s page=%d; prior_pages=%d',
                        query, start, end, len(state['pages']) + 1, len(state['pages']))
            payload, error, source = core.fetch_x_api_endpoint_payload_with_app_auth(
                self.auths[0], f'{core.X_API_BASE_URL}/tweets/search/all', params, 'precision search')
            if not isinstance(payload, dict):
                raise PrecisionError(f'X API search failed for {query!r}: {error or "invalid response"}; '
                                     'already completed pages remain in the checkpoint.')
            new_next = accept_page(payload, source)
            self._event('info', 'SEARCH API page received: query=%r page=%d records=%d has_next=%s source=%s',
                        query, len(state['pages']) + 1, len(payload.get('data', []) or []), bool(new_next), source)
            if new_next and (new_next == next_token or new_next in seen_tokens):
                raise PrecisionError('Repeated X API pagination token; stopped to avoid duplicate paid requests.')
            state['pages'].append({'payload': payload, 'source': source})
            state['next_token'] = new_next
            state['complete'] = not bool(new_next)
            state['saved_at'] = datetime.now(timezone.utc).isoformat()
            self.cache_dir.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=self.cache_dir,
                                             prefix='.precision-page-', suffix='.tmp', delete=False) as out:
                temporary = Path(out.name)
                json.dump(state, out, ensure_ascii=False)
                out.flush()
                os.fsync(out.fileno())
            try:
                os.replace(temporary, checkpoint_path)
            finally:
                temporary.unlink(missing_ok=True)
            self._event('debug', 'SEARCH checkpoint saved: %s page=%d complete=%s',
                        checkpoint_path, len(state['pages']), state['complete'])
            if not new_next:
                break
            seen_tokens.add(new_next)
            next_token = new_next
        self.search_cache[key] = collected
        self._event('info', 'SEARCH complete: query=%r pages=%d posts=%d',
                    query, len(state['pages']), len(collected))
        return collected

    def _id_lookup(self, tid: str) -> tuple[dict, str]:
        if tid in self.api_cache:
            self._event('debug', 'ID lookup cached: id=%s', tid)
            return self.api_cache[tid]
        self.request_count += 1
        self._event('info', 'ID API lookup: id=%s', tid)
        payload, error, source = core.fetch_x_api_tweet_payload_with_auths(self.auths, tid)
        if not isinstance(payload, dict) or not primary_node(payload, tid):
            raise PrecisionError(f'X API cannot retrieve {tid}: {error or "missing post"}')
        self.api_cache[tid] = (payload, source)
        self._event('info', 'ID API lookup succeeded: id=%s source=%s', tid, source)
        self._cache_expanded_tweets(payload.get('includes', {}), source)
        return payload, source

    def resolve(self, tid: str, *, first_id: bool = False, hint: str = '') -> tuple[dict, str]:
        """Main ID: local then paid API. Parents: local -> cached API -> Wayback -> paid API."""
        if tid in self.resolved_cache:
            return self.resolved_cache[tid]
        local = self.local.get(tid)
        if local is not None:
            result = (local, 'local_json')
        elif tid in self.api_cache:
            result = self.api_cache[tid]
        elif first_id or self.x_api_only:
            result = self._id_lookup(tid)
        else:
            parent, error, source = core.fetch_wayback_tweet_payload(tid, hint)
            if isinstance(parent, dict) and primary_node(parent, tid):
                result = (parent, source)
            else:
                result = self._id_lookup(tid)
        if not primary_node(result[0], tid):
            raise PrecisionError(f'Retrieved object does not contain target post {tid}.')
        self._event('debug', 'RESOLVE id=%s source=%s first_id=%s', tid, result[1], first_id)
        self.resolved_cache[tid] = result
        return result

    def _root(self, tid: str, payload: dict) -> tuple[str, dict]:
        """Find the true root; never validate a reply author as its root.

        A Wayback JSON may omit conversation_id. In that case follow its
        reply-parent links before author verification, reusing local/Wayback
        first. If an ancestor cannot be resolved, reject rather than guess.
        """
        node = primary_node(payload, tid)
        if node is None:
            raise PrecisionError(f'Cannot identify tweet {tid} for root verification.')
        meta = core._extract_metadata_from_node(node)
        root_id = str(meta.get('conversation_id') or '')
        immediate_parent = reply_parent(node)
        if root_id and not root_id.isdigit():
            raise PrecisionError(f'Invalid conversation root ID for {tid}.')
        if root_id and (root_id != tid or not immediate_parent):
            if root_id == tid:
                return tid, payload
            root_payload, _ = self.resolve(root_id, hint=self.target)
            return root_id, root_payload
        # Root ID absent, or a contradictory conversation_id == tweet ID on a
        # reply: walk up until a genuine original post is reached.
        current_id, current_payload = tid, payload
        visited = {tid}
        while True:
            node = primary_node(current_payload, current_id)
            if node is None:
                raise PrecisionError(f'Cannot inspect ancestor {current_id}.')
            parent = reply_parent(node)
            if not parent:
                return current_id, current_payload
            if not parent.isdigit() or parent in visited:
                raise PrecisionError(f'Invalid or cyclic reply chain at {current_id}.')
            visited.add(parent)
            current_payload, _ = self.resolve(parent, hint=self.target)
            current_id = parent
            parent_root = str(core._extract_metadata_from_node(
                primary_node(current_payload, current_id)).get('conversation_id') or '')
            if parent_root and parent_root.isdigit() and parent_root != current_id:
                root_payload, _ = self.resolve(parent_root, hint=self.target)
                return parent_root, root_payload

    def _verify_id_root(self, root_id: str, payload: dict, *, local_root: bool = False) -> str:
        node = primary_node(payload, root_id)
        if not node:
            raise PrecisionError(f'Cannot validate root author for {root_id}.')
        username, uid, _ = author_identity(payload, node)
        if local_root and self.mode == 2:
            if username.casefold() == self.target.casefold():
                known_ids = {u for _, u, _ in self.local.history if u}
                if uid and (not known_ids or known_ids == {uid}):
                    return uid
                raise PrecisionError('Local root author ID conflicts with existing target-account history; refusing to guess.')
            # A historical account may have multiple former usernames; match account ID.
            historical = self.local.historical_user(primary_time(node), uid)
            if historical and uid and any(old_uid == uid for _, old_uid, _ in self.local.history):
                return uid
            raise PrecisionError(f'Local root @{username} does not match @{self.target} by author ID; aborting without prompting.')
        if username.casefold() == self.target.casefold():
            return uid
        print(f'Root post {root_id} is by @{username or "(unknown)"}, not @{self.target}.')
        answer = input('Continue with an alternate/renamed username? Enter Y to continue, otherwise abort: ').strip().lower()
        if answer not in ('y', 'yes'):
            raise PrecisionError('User declined author mismatch; no new JSON written for this ID.')
        expected_uid = input('Enter target account author_id for verification: ').strip()
        if not expected_uid.isdigit():
            raise PrecisionError('Invalid author_id; rejected.')
        if not uid:
            # Only this case needs a paid root lookup to verify an unknown legacy ID.
            api, _ = self._id_lookup(root_id)
            _, uid, _ = author_identity(api, primary_node(api, root_id))
        if not uid or uid != expected_uid:
            raise PrecisionError(f'Author ID mismatch for root {root_id}; rejected.')
        self.target_author_ids.add(uid)
        return uid

    def _historical_rewrite(self, payload: dict, target_id: str, created: datetime) -> dict:
        if not target_id:
            return payload
        # Time-range NewName intentionally has NO username/author-ID validation.
        old = (deepcopy(self.pinned_root_profiles.get(target_id))
               or self.local.historical_user(created, target_id))
        if not old or not old.get('username'):
            raise PrecisionError('No suitable local historical user profile for newly fetched target-account post; not writing it.')
        includes = payload.get('includes', {})
        if not isinstance(includes, dict):
            return payload
        for user in includes.get('users', []) or []:
            if isinstance(user, dict) and str(user.get('id')) == target_id:
                # Replace only compatible v2 fields; ID must always match API identity.
                keep_id = user['id']
                for field in ('username', 'name', 'profile_image_url', 'description',
                              'location', 'url', 'created_at', 'protected', 'verified',
                              'entities', 'public_metrics'):
                    if field in old and old[field] not in ('', None):
                        user[field] = deepcopy(old[field])
                user['id'] = keep_id
        return payload

    def _save(self, tid: str, payload: dict, source: str = '') -> Optional[object]:
        if self.local.existing_main(tid):
            self.skipped += 1
            self._event('debug', 'SKIP existing JSON: id=%s', tid)
            return None
        node = primary_node(payload, tid)
        if not node:
            self.errors.append(f'{tid}: no usable tweet node; not saved')
            return None
        try:
            published = primary_time(node)
        except PrecisionError as exc:
            self.errors.append(f'{tid}: {exc}')
            return None
        ts = published.strftime('%Y%m%d%H%M%S')
        # A local JSON may contain this tweet only in includes/referenced tweets.
        # NEVER write that container's unrelated primary tweet under this ID.
        # Normalize to an independent snapshot whose primary data is the target.
        data = deepcopy(payload)
        actual_main = data.get('data')
        if not isinstance(actual_main, dict) or str(actual_main.get('id', '')) != tid:
            picked = deepcopy(node)
            own_includes = slim_includes(picked, data.get('includes', {}))
            data = {'data': picked, 'includes': own_includes}
        author_name, author_uid, _ = author_identity(data, primary_node(data, tid))
        # A reply by another person can contain the target account in
        # includes.users (in_reply_to_user_id). Restore that user too, NEVER
        # the reply author's own profile.
        included = data.get('includes', {}).get('users', []) if isinstance(data.get('includes'), dict) else []
        profile_ids = {str(u.get('id', '')) for u in included if isinstance(u, dict)}
        restore_ids = self.target_author_ids.intersection(profile_ids)
        if self.newname and author_uid in self.target_author_ids and author_uid not in profile_ids:
            self.errors.append(f'{tid}: missing expanded target-author user profile; refusing to save uncorrected NewName JSON')
            return None
        if self.newname:
            try:
                for target_id in restore_ids:
                    self._historical_rewrite(data, target_id, published)
            except PrecisionError as exc:
                self.errors.append(f'{tid}: {exc}')
                return None
        metadata = core._get_x_api_json_cache(data, create=True)
        metadata.update({'source': 'precision_' + ('wayback' if 'wayback' in source else 'x_api'),
                         'archive_user': self.target, 'fetched_at': core._utc_now_iso()})
        # Unknown authors should never be attributed to the archive owner.
        original_url = core.reconstruct_original_url(author_name or 'i', tid)
        if self.newname and author_uid in restore_ids:
            for u in data.get('includes', {}).get('users', []):
                if isinstance(u, dict) and str(u.get('id')) == author_uid and u.get('username'):
                    original_url = core.reconstruct_original_url(str(u['username']), tid)
                    break
        path = core.build_json_output_path(self.json_dir, ts, original_url, {'tweet_id': tid})
        if path.exists() or tid in self.local.occupied:
            self.errors.append(f'{tid}: filename/ID already occupied by an existing invalid JSON; skipped without overwrite')
            return None
        self.json_dir.mkdir(parents=True, exist_ok=True)
        # O_EXCL ensures even another process cannot overwrite an existing file.
        try:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        except FileExistsError:
            self.errors.append(f'{tid}: another file already exists; not overwritten')
            return None
        try:
            with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as file:
                json.dump(data, file, ensure_ascii=False, indent=2)
                file.write('\n')
                file.flush()
                os.fsync(file.fileno())
        except Exception:
            path.unlink(missing_ok=True)
            raise
        record = core.SnapshotRecord(timestamp=ts, original_url=original_url, json_path=path)
        self.local.add(tid, path, data)
        self.written_records.append(record)
        self.new_ids.add(tid)
        self._event('info', 'SAVE new JSON: id=%s path=%s source=%s', tid, path, source)
        return record

    def _parents(self, start_id: str, start_payload: dict) -> dict:
        """Attach upper reply chain to a NEW primary JSON, in the core format.

        Unlike descendants (which the original tool saves as snapshots), upper
        ancestors are context, not independent archive timeline entries.  The
        repaired original downloader stores these in
        _pale_fire.x_api_reply_chains[start_id].posts; use its own writer.
        Never persist this enriched copy over an existing JSON.
        """
        enriched = deepcopy(start_payload)
        node = primary_node(enriched, start_id)
        if not node:
            return enriched
        curr_id, curr = start_id, enriched
        # The core reader requests the cache by the *immediate parent ID*.
        # Its entries are keyed by the first referenced_tweet id, NOT by the
        # seed tweet's ID (see append_x_api_reply_chain in the core source).
        chain_key = reply_parent(node)
        traversed = {curr_id}
        chain = []
        missing_id = ''
        missing_error = ''
        while True:
            node = primary_node(curr, curr_id)
            if node is None:
                break
            parent_id = reply_parent(node)
            if not parent_id:
                break
            if parent_id in traversed or not parent_id.isdigit():
                missing_id = parent_id
                missing_error = 'Invalid or cyclic ancestor chain'
                break
            traversed.add(parent_id)
            try:
                ancestor, source = self.resolve(
                    parent_id, hint=core._extract_metadata_from_node(node).get('in_reply_to_screen_name') or '')
            except PrecisionError as exc:
                missing_id, missing_error = parent_id, str(exc)
                break
            # Work on a copy: ancestor may be an unchanged local primary JSON.
            parent_payload = deepcopy(ancestor)
            if self.newname:
                # Rewriting the seed's top-level includes is not enough when a
                # target-account post appears as a parent, nested in the cache.
                # Restore only target-account user profiles, never other authors.
                parent_node = primary_node(parent_payload, parent_id)
                parent_time = None
                try:
                    parent_time = primary_time(parent_node)
                except PrecisionError:
                    pass
                inc = parent_payload.get('includes', {})
                if parent_time and isinstance(inc, dict):
                    local_ids = {str(u.get('id')) for u in inc.get('users', []) or []
                                 if isinstance(u, dict)}
                    for uid in self.target_author_ids.intersection(local_ids):
                        try:
                            self._historical_rewrite(parent_payload, uid, parent_time)
                        except PrecisionError as exc:
                            self.errors.append(f'Cached parent {parent_id}: {exc}')
            chain.append((parent_id, parent_payload, source))
            curr_id, curr = parent_id, parent_payload
        if chain or missing_error:
            core._store_x_api_reply_chain(
                enriched, chain_key, len(chain), chain,
                terminal_error_id=missing_id,
                terminal_error_message=missing_error,
            )
        if missing_error:
            self.errors.append(f'Parent {missing_id} of seed {start_id}: {missing_error}; saved partial reply-chain context')
        self._event('info', 'PARENTS seed=%s resolved=%d incomplete=%s', start_id, len(chain), bool(missing_error))
        return enriched

    def _descendants(self, seed_ids: list[str]) -> None:
        todo = deque(seed_ids)
        while todo:
            parent_id = todo.popleft()
            if parent_id in self.children_done:
                continue
            self.children_done.add(parent_id)
            self._event('info', 'DESCENDANTS search parent=%s', parent_id)
            print(f'Direct reply search under {parent_id}...', flush=True)
            # NO conversation_id query or fallback: only the selected branch.
            # The reply-parent check below excludes non-replies without
            # excluding reposts/quotes from the time-range seed search.
            posts = self._request_search(f'in_reply_to_tweet_id:{parent_id}')
            valid_children = 0
            for tweet, includes in posts:
                tid = str(tweet['id'])
                if reply_parent(tweet) != parent_id:
                    continue
                valid_children += 1
                payload = {'data': tweet, 'includes': includes}
                self._save(tid, payload, 'x_api_direct_reply_search')
                todo.append(tid)
            self._event('info', 'DESCENDANTS result parent=%s returned=%d actual_children=%d',
                        parent_id, len(posts), valid_children)

    def run_ids(self, ids: list[str]) -> None:
        seen = set()
        for tid in ids:
            if tid in seen:
                continue
            seen.add(tid)
            self._event('info', 'SEED ID started: id=%s mode=%d', tid, self.mode)
            # No account identity or pinned root profile leaks between IDs.
            self.target_author_ids.clear()
            self.pinned_root_profiles.clear()
            if self.local.existing_main(tid) and self.mode == 1:
                self.skipped += 1
                self._event('info', 'SEED ID skipped existing JSON: id=%s', tid)
                print(f'{tid}: existing main JSON reused unchanged; no X API query or parent-chain modification.')
                continue
            try:
                data, source = self.resolve(tid, first_id=True)
                node = primary_node(data, tid)
                if self.mode == 2 and (reply_parent(node) or (core._extract_metadata_from_node(node).get('conversation_id') not in ('', tid))):
                    raise PrecisionError(f'Mode 2 requires an original/root tweet ID: {tid} is a reply.')
                root_id, root_payload = self._root(tid, data)
                local_root = self.local.existing_main(root_id)
                uid = self._verify_id_root(root_id, root_payload, local_root=local_root)
                if uid:
                    self.target_author_ids.add(uid)
                if self.mode == 2 and local_root and uid:
                    _, profile_uid, profile = author_identity(
                        root_payload, primary_node(root_payload, root_id))
                    if profile_uid != uid or not profile.get('username'):
                        raise PrecisionError('Local root profile incomplete; cannot safely restore account metadata.')
                    self.pinned_root_profiles[uid] = profile
                # For ID-mode username mismatch, historical rewrite is needed even
                # though the time-range NewName toggle isn't used.
                root_author, _, _ = author_identity(root_payload, primary_node(root_payload, root_id))
                original_newname = self.newname
                if root_author.casefold() != self.target.casefold() or (local_root and self.mode == 2):
                    # Mode 2 with a local root always restores the target's
                    # historical profile on NEW descendants, even if the API
                    # currently reports a different username.
                    self.newname = True
                    if not self.local.history:
                        raise PrecisionError('No local target-account history to restore.')
                if not self.local.existing_main(tid):
                    self._save(tid, self._parents(tid, data), source)
                if self.mode == 2:
                    self._descendants([tid])
                self.newname = original_newname
                self.pinned_root_profiles.clear()
            except PrecisionError as exc:
                self.errors.append(f'{tid}: {exc}')
                print(f'{tid}: rejected/failed: {exc}', flush=True)
                # Never carry a temporary NewName flag to another ID.
                self.newname = False
                self.pinned_root_profiles.clear()

    def run_time(self, start: str, end: str) -> None:
        if start >= end:
            raise PrecisionError('End time must be later than start time.')
        query = f'from:{self.api_username}'
        print(f'Searching @{self.api_username} {start} <= created_at < {end} (UTC)...', flush=True)
        posts = self._request_search(query, start, end)
        self._event('info', 'TIME RANGE matched=%d user=@%s start=%s end=%s', len(posts), self.api_username, start, end)
        seed_ids = []
        for tweet, includes in posts:
            tid = str(tweet['id'])
            uid = str(tweet.get('author_id') or '')
            if uid:
                self.target_author_ids.add(uid)
            payload = {'data': tweet, 'includes': includes}
            if not self.local.existing_main(tid):
                self._save(tid, self._parents(tid, payload), 'x_api_time_search')
            else:
                self.skipped += 1
            seed_ids.append(tid)
        if self.mode == 2:
            self._descendants(seed_ids)

    def finish(self) -> None:
        if self.written_records:
            self._event('info', 'MANIFEST update starting: new_records=%d', len(self.written_records))
            self._update_manifest()
            if not self.json_only:
                # Existing media tool is reused only for NEW JSON.  No bearer is
                # passed: missing media cannot trigger extra *paid* tweet reads.
                print('Downloading media referenced by newly archived JSON...', flush=True)
                try:
                    stats = core.repair_missing_media_from_snapshot_records(
                        self.written_records, self.asset_dir, workers=8,
                        x_bearer_token='', resume=True,
                        allow_wayback_media_fallback=not self.x_api_only,
                        media_fetch_policy=(
                            replace(core.MEDIA_FETCH_FULL,
                                    allow_wayback_fallback=False,
                                    allow_closest_cdx_lookup=False)
                            if self.x_api_only else core.MEDIA_FETCH_FULL
                        ),
                    )
                    print('Media targets / missing / repaired / remaining:', stats, flush=True)
                    self._event('info', 'MEDIA summary total/missing/repaired/remaining=%s', stats)
                    if isinstance(stats, (tuple, list)) and len(stats) >= 4 and isinstance(stats[3], int) and stats[3] > 0:
                        self.errors.append(f'Media incomplete: {stats[3]} targets still missing after repair attempts; '
                                           f'see original media negative cache and media files under {self.asset_dir}')
                except Exception as exc:
                    self._event('error', 'MEDIA repair exception: %s', exc, exc_info=True)
                    self.errors.append(f'Media repair failed: {type(exc).__name__}: {exc}')
        summary = (f'Precision finished: {len(self.new_ids)} new JSON; {self.skipped} reused; '
                   f'{self.request_count} X API lookup/search operations attempted; {len(self.errors)} warning(s).')
        print(summary, flush=True)
        self._event('info', '%s', summary)
        for err in self.errors:
            print('WARNING:', err, flush=True)
        print('Existing JSON files were not overwritten; HTML was not regenerated.', flush=True)

    def _update_manifest(self) -> None:
        manifest = core.snapshot_manifest_path(self.asset_dir)
        if manifest.exists():
            try:
                data = json.loads(manifest.read_text(encoding='utf-8'))
            except Exception as exc:
                self.errors.append(f'Cannot parse existing manifest; left untouched: {exc}')
                return
            if not isinstance(data, dict) or not isinstance(data.get('snapshots'), list):
                self.errors.append('Unexpected manifest format; left untouched.')
                return
        else:
            data = {'user': self.target, 'snapshots': []}
        filenames = {x.get('json_filename') for x in data['snapshots'] if isinstance(x, dict)}
        # CRITICAL: the original tool reads ONLY snapshots.json when present.
        # Seeding a new manifest with just new files would hide ALL old JSON.
        # Preserve original manifest entries, then include every valid existing
        # snapshot on disk, including files created before this patch.
        for path in sorted(self.json_dir.glob('*.json')):
            if path.name in filenames:
                continue
            parsed = core.parse_snapshot_filename(path.name)
            if not parsed:
                continue
            ts, tid = parsed
            payload = core.load_snapshot_json(path)
            node = primary_node(payload, tid) if isinstance(payload, dict) else None
            if not node:
                continue
            author, _, _ = author_identity(payload, node)
            data['snapshots'].append({
                'timestamp': ts,
                'original_url': core.reconstruct_original_url(author or 'i', tid),
                'json_filename': path.name,
            })
            filenames.add(path.name)
        manifest.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=manifest.parent,
                                         prefix='.precision-manifest-', suffix='.tmp', delete=False) as out:
            tmp = Path(out.name)
            json.dump(data, out, ensure_ascii=False, indent=2)
            out.write('\n')
            out.flush()
            os.fsync(out.fileno())
        try:
            os.replace(tmp, manifest)
        finally:
            tmp.unlink(missing_ok=True)
        self._event('info', 'MANIFEST updated: path=%s snapshots=%d', manifest, len(data['snapshots']))



def read_id_file(filename: str) -> list[str]:
    raw_ids = []
    for line in Path(filename).read_text(encoding='utf-8-sig').splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        raw_ids.append(clean_id(line))
    return raw_ids


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description='Exact-ID or UTC date-range X API supplement; no existing JSON overwrites.')
    parser.add_argument('twitter_username', help='Local archive username (OldName permitted).')
    choices = parser.add_mutually_exclusive_group(required=True)
    choices.add_argument('--precision-ids', nargs='+', action='append', metavar='ID', help='One or more tweet IDs / status URLs; can repeat.')
    choices.add_argument('--precision-file', metavar='TXT', help='One tweet ID per line.')
    choices.add_argument('--precision-start', metavar='UTC_DATE', help='UTC start, inclusive.')
    parser.add_argument('--precision-end', metavar='UTC_DATE', help='UTC end: date inclusive, time exclusive.')
    parser.add_argument('--precision-api-username', metavar='NAME', help='Username to query; REQUIRED with date range.')
    parser.add_argument('--precision-mode', required=True, type=int, choices=[1, 2], help='1=parents only; 2=parents + direct-descendant reply tree.')
    parser.add_argument('--precision-env-file', action='append', metavar='ENV', help='Credentials .env; repeatable; default .env.')
    parser.add_argument('--precision-json-only', action='store_true', help='Do not download new media.')
    parser.add_argument('--precision-x-api-only', action='store_true', help='Do not use Wayback for missing parent posts.')
    args = parser.parse_args(argv)
    diagnostics = None
    job = None
    try:
        target = clean_user(args.twitter_username)
        time_mode = args.precision_start is not None
        if time_mode:
            if not args.precision_end or not args.precision_api_username:
                parser.error('--precision-start requires --precision-end and --precision-api-username.')
            api_name = clean_user(args.precision_api_username)
            start = parse_date_arg(args.precision_start)
            end = parse_date_arg(args.precision_end, is_end=True)
            if start >= end:
                parser.error('End time must follow start time.')
            different = target.casefold() != api_name.casefold()
            if different:
                print(f'Archive target @{target}; API query @{api_name}: NewName mode is required.')
                confirmation = input('Confirm NewName mode? Enter Y to continue, any other input to cancel: ').strip().lower()
                if confirmation not in ('y', 'yes'):
                    print('NewName mode declined. No API query performed.')
                    return 1
            newname = different
            ids = []
        else:
            if args.precision_end or args.precision_api_username:
                parser.error('--precision-end / --precision-api-username apply only with --precision-start.')
            if args.precision_file:
                ids = read_id_file(args.precision_file)
            else:
                ids = [clean_id(x) for group in args.precision_ids or [] for value in group for x in value.split(',') if x.strip()]
            if not ids:
                parser.error('No IDs given.')
            api_name = ''
            newname = False
        files = args.precision_env_file or ['.env']
        diagnostics = RunDiagnostics(core.build_output_paths(target)[1], target)
        print(f'Precision run log: {diagnostics.run_path}', flush=True)
        print(f'Precision error log: {diagnostics.error_path}', flush=True)
        diagnostics.logger.info('Operation=%s mode=%d target=@%s api_username=@%s newname=%s json_only=%s x_api_only=%s',
                                'time_range' if time_mode else 'ids', args.precision_mode, target,
                                api_name, newname, args.precision_json_only, args.precision_x_api_only)
        if time_mode:
            diagnostics.logger.info('Time range UTC start=%s end=%s', start, end)
        else:
            diagnostics.logger.info('ID count=%d; IDs=%s', len(ids), ','.join(ids))
        job = PrecisionJob(target=target, mode=args.precision_mode, api_username=api_name,
                           newname=newname, json_only=args.precision_json_only,
                           x_api_only=args.precision_x_api_only, env_files=files,
                           diagnostics=diagnostics)
        core.set_x_api_min_interval(core.parse_float_env('X_API_MIN_INTERVAL_SECONDS', core.DEFAULT_X_API_MIN_INTERVAL_SECONDS))
        try:
            if time_mode:
                job.run_time(start, end)
            else:
                job.run_ids(ids)
        except KeyboardInterrupt:
            job.errors.append('Run interrupted by user; partial archive and search checkpoints may exist')
            raise
        finally:
            # Retain existing behavior: always finalize JSONs already saved.
            job.finish()
        return 1 if job.errors else 0
    except (PrecisionError, KeyboardInterrupt) as exc:
        if diagnostics is not None:
            diagnostics.logger.error('RUN STOPPED: %s: %s', type(exc).__name__, exc)
        print(f'Precision stopped: {exc}', file=sys.stderr)
        return 1
    except Exception as exc:
        if diagnostics is not None:
            diagnostics.logger.exception('UNEXPECTED RUN FAILURE: %s: %s', type(exc).__name__, exc)
        print(f'Precision unexpected failure ({type(exc).__name__}): {exc}', file=sys.stderr)
        return 1
    finally:
        if diagnostics is not None:
            diagnostics.logger.info('Log files: run=%s errors=%s', diagnostics.run_path, diagnostics.error_path)
            diagnostics.close()


if __name__ == '__main__':
    sys.exit(main())
