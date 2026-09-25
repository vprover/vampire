"""Validate emitted obligations with Z3 and reparse transformed TPTP inputs."""
import json
from pathlib import Path
import re
import subprocess


def validate_smt_script(text, folder, z3, timeout):
    starts = re.findall(r'^% SZS output start Proof.*$', text, re.M)
    ends = re.findall(r'^% SZS output end Proof.*$', text, re.M)
    if len(starts) != 1 or len(ends) != 1:
        return 'fail', 'missing or ambiguous proof boundaries'
    body = text.split(starts[0], 1)[1].split(ends[0], 1)[0]
    if body.lstrip().startswith('(set-logic') is False:
        return 'fail', 'proof is not an SMT script'
    obligations = len(re.findall(r'^\s*\(check-sat\)\s*$', body, re.M))
    unsupported = re.findall(r'\(echo "sorry: ([^"]+)"\)', body)
    (folder / 'proof.smt2').write_text(body)
    if not obligations:
        return 'inconclusive', 'no checkable proof obligations'
    command = [str(z3), str(folder / 'proof.smt2')]
    (folder / 'validator-command.json').write_text(json.dumps(command, indent=2))
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        (folder / 'validator.stdout').write_bytes(error.stdout or b'')
        (folder / 'validator.stderr').write_bytes(error.stderr or b'')
        return 'inconclusive', 'independent proof checker timed out'
    except OSError as error:
        return 'inconclusive', f'independent proof checker unavailable: {error}'
    (folder / 'validator.stdout').write_text(result.stdout)
    (folder / 'validator.stderr').write_text(result.stderr)
    answers = [line.strip() for line in result.stdout.splitlines() if line.strip() in ('sat', 'unsat', 'unknown')]
    (folder / 'proof-validation.json').write_text(json.dumps({
        'obligations': obligations, 'answers': answers, 'unsupported_rules': unsupported,
        'scope': 'Emitted inference obligations only; skipped input/definition introduction is not independently certified.'}, indent=2))
    if result.returncode != 0 or '(error ' in result.stdout or result.stderr.strip():
        return 'fail', 'independent checker rejected the emitted script'
    if 'sat' in answers: return 'fail', 'independent checker found a satisfiable proof obligation'
    if len(answers) != obligations: return 'fail', 'proof obligation/answer count mismatch'
    if 'unknown' in answers: return 'inconclusive', 'independent checker returned unknown'
    if unsupported: return 'inconclusive', 'unsupported proof rules: ' + ', '.join(sorted(set(unsupported)))
    return 'pass', ''


def validate_roundtrip(text, folder, binary, expected, timeout, run_solver=None, unlimited_memory=False):
    noncomments = '\n'.join(line for line in text.splitlines() if not line.lstrip().startswith('%')).strip()
    if noncomments and not re.search(r'^(?:cnf|fof|tff|tcf|thf)\(', text, re.M):
        return 'fail', 'transformation emitted no TPTP units'
    path = folder / 'transformed.p'
    path.write_text(text)
    command = [str(binary), '--input_syntax', 'tptp', '-t', '5', '-p', 'off', str(path)]
    if unlimited_memory: command += ['-m', '0']
    (folder / 'validator-command.json').write_text(json.dumps(command, indent=2))
    if run_solver is not None:
        # Reuse process-group timeouts and instrumentation from the primary run.
        result = run_solver(command)
        return result['semantic_outcome'], result['semantic_reason']
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        (folder / 'validator.stdout').write_bytes(error.stdout or b'')
        (folder / 'validator.stderr').write_bytes(error.stderr or b'')
        return 'inconclusive', 'reparsed problem timed out'
    (folder / 'validator.stdout').write_text(result.stdout)
    (folder / 'validator.stderr').write_text(result.stderr)
    from diagnostics import sanitizer_messages, sanitizer_warnings, ASSERTION
    if sanitizer_messages(result.stdout, result.stderr) or ASSERTION.search(result.stdout + result.stderr):
        return 'fail', 'reparsed problem triggered an assertion or sanitizer'
    answers = re.findall(r'^% SZS status (\w+)', result.stdout, re.M)
    warnings = sanitizer_warnings(result.stdout, result.stderr)
    if answers == [expected] and warnings:
        return 'inconclusive', 'reparsed problem: sanitizer leak check needs confirmation'
    if result.returncode == 0 and answers == [expected]: return 'pass', ''
    if any(a in ('Timeout', 'ResourceOut', 'GaveUp') for a in answers) or 'Termination reason: Time limit' in result.stdout:
        return 'inconclusive', 'reparsed problem reached a solver limit'
    return 'fail', f'reparsed problem: expected {expected}, got {answers}, exit {result.returncode}'
