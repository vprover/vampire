#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
profile=${1:-coverage}
configure_only=${2:-}
if test "$#" -gt 2 || { test -n "$configure_only" && test "$configure_only" != --configure-only; }; then
  echo "usage: $0 [profile] [--configure-only]" >&2
  exit 2
fi
jobs=${JOBS:-4}
build="build/testing/$profile"
# Reset profile-specific cache values so reconfiguration cannot retain stale flags.
args=(-S . -B "$build" -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
  -DCHECK_LEAKS=ON -DUBSAN=OFF -DCOVERAGE=OFF -DCMAKE_DISABLE_FIND_PACKAGE_Z3=OFF
  -DCMAKE_CXX_FLAGS= -DCMAKE_EXE_LINKER_FLAGS=)
if test -n "${Z3_DIR:-}"; then args+=("-DZ3_DIR=$Z3_DIR"); fi
case "$profile" in
  coverage)
    args+=(-DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON
      '-DCMAKE_CXX_FLAGS=--coverage -fprofile-update=atomic'
      -DCMAKE_EXE_LINKER_FLAGS=--coverage)
    targets=(vampire vtest) ;;
  debug|memcheck)
    args+=(-DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON)
    targets=(vampire vtest) ;;
  ubsan)
    args+=(-DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON -DUBSAN=ON
      -DCMAKE_CXX_FLAGS=-fno-sanitize-recover=undefined)
    targets=(vampire vtest) ;;
  asan)
    args+=(-DCMAKE_BUILD_TYPE=Debug -DCHECK_LEAKS=ON
      '-DCMAKE_CXX_FLAGS=-fsanitize=address -fno-omit-frame-pointer'
      -DCMAKE_EXE_LINKER_FLAGS=-fsanitize=address)
    targets=(vampire vtest) ;;
  release)
    args+=(-DCMAKE_BUILD_TYPE=Release -DCHECK_LEAKS=OFF)
    targets=(vampire) ;;
  no-z3)
    args+=(-DCMAKE_BUILD_TYPE=Debug -DCMAKE_DISABLE_FIND_PACKAGE_Z3=ON)
    targets=(vampire vtest) ;;
  *) echo "unknown profile: $profile" >&2; exit 2 ;;
esac
cmake "${args[@]}"
python3 checks/testing/build_profile.py --build "$build" --profile "$profile"
if test "$configure_only" = --configure-only; then exit 0; fi
cmake --build "$build" --target "${targets[@]}" -j "$jobs"
