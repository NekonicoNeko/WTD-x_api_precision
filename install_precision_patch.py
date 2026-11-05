#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Safe launcher install/upgrade for versioned x_api_precision(8).py.

The delivered file keeps its (8) suffix.  Installer copies it to the runtime
module filename x_api_precision.py with a unique backup if one already exists.
It only patches the original download_archive.py's final __main__ block.
"""
from __future__ import annotations
import argparse
from datetime import datetime
from pathlib import Path
import os
import sys

ANCHOR = 'if __name__ == "__main__":\n    main()'
PATCH = '''if __name__ == "__main__":
    if any(arg.startswith("--precision-") for arg in sys.argv[1:]):
        from x_api_precision import main as precision_main
        sys.exit(precision_main(sys.argv[1:]))
    main()'''


def main() -> int:
    parser = argparse.ArgumentParser(description='Install or upgrade precision module v8; back up existing files.')
    parser.add_argument('--file', type=Path, default=Path(__file__).resolve().parent / 'download_archive.py',
                        help='Current repaired download_archive.py; default: beside installer.')
    parser.add_argument('--uninstall', action='store_true', help='Undo only the launcher entry patch, not archive data.')
    args = parser.parse_args()
    path = args.file.resolve()
    if not path.is_file():
        print(f'Missing repaired source: {path}', file=sys.stderr)
        return 1
    raw = path.read_bytes()
    bom = raw.startswith(b'\xef\xbb\xbf')
    try:
        original = raw.decode('utf-8-sig')
    except UnicodeError:
        print('Repaired script is not UTF-8; no modifications made.', file=sys.stderr)
        return 1
    newline = '\r\n' if b'\r\n' in raw else '\n'
    normalized = original.replace('\r\n', '\n')
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S_%f')

    if args.uninstall:
        if normalized.count(PATCH) != 1:
            print('Exact installed entry patch not present; refusing to modify.', file=sys.stderr)
            return 1
        updated = normalized.replace(PATCH, ANCHOR)
        to_upgrade_module = None
    else:
        source = path.with_name('x_api_precision(8).py')
        if not source.is_file():
            print(f'Place the versioned module beside the repaired source first: {source}', file=sys.stderr)
            return 1
        try:
            module_bytes = source.read_bytes()
            compile(module_bytes, str(source), 'exec')
        except Exception as exc:
            print(f'Versioned module syntax check failed: {exc}', file=sys.stderr)
            return 1
        to_upgrade_module = (path.with_name('x_api_precision.py'), module_bytes)
        if normalized.count(PATCH) == 1:
            updated = normalized
        elif normalized.count(ANCHOR) == 1 and normalized.rstrip().endswith(ANCHOR):
            if ('def fetch_x_api_endpoint_payload_with_app_auth(' not in normalized
                    or 'def fetch_wayback_tweet_payload(' not in normalized):
                print('Expected repaired helpers absent; source untouched.', file=sys.stderr)
                return 1
            updated = normalized.replace(ANCHOR, PATCH)
        else:
            print('Unexpected launcher structure; no files modified.', file=sys.stderr)
            return 1

    modified_core = updated != normalized
    output = ('\ufeff' if bom else '') + updated.replace('\n', newline)
    try:
        compile(output, str(path), 'exec')
    except Exception as exc:
        print(f'Launcher compilation failed: {exc}', file=sys.stderr)
        return 1

    module_modified = (to_upgrade_module is not None
                       and (not to_upgrade_module[0].exists()
                            or to_upgrade_module[0].read_bytes() != to_upgrade_module[1]))
    if not modified_core and not module_modified:
        print('Precision v8 already installed; no changes.')
        return 0

    # Prepare every backup before the first replacement.
    for target, needs_backup in ((path, modified_core),
                                 (to_upgrade_module[0] if to_upgrade_module else path, module_modified)):
        if needs_backup and target.exists():
            backup = target.with_name(f'{target.name}.before_precision_{stamp}.bak')
            with backup.open('xb') as out:
                out.write(target.read_bytes())
            print(f'Backed up {target.name} -> {backup.name}')

    if module_modified and to_upgrade_module:
        runtime, content = to_upgrade_module
        staged = runtime.with_name(f'.{runtime.name}.precision_{stamp}.tmp')
        try:
            with staged.open('xb') as out:
                out.write(content)
                out.flush()
                os.fsync(out.fileno())
            staged.replace(runtime)
        finally:
            staged.unlink(missing_ok=True)
        print(f'Installed versioned module {source.name} -> runtime {runtime.name}')

    if modified_core:
        staged = path.with_name(f'.{path.name}.precision_{stamp}.tmp')
        try:
            with staged.open('x', encoding='utf-8', newline='') as out:
                out.write(output)
                out.flush()
                os.fsync(out.fileno())
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
        print('Repaired main script entry-point updated.')
    elif args.uninstall:
        print('Entry point not modified.')
    else:
        print('Existing precision entry-point reused without changes.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
