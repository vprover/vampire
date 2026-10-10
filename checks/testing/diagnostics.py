"""Separate solver answers from instrumentation failures."""
import re

SANITIZER = re.compile(r'(?:ERROR: (?:AddressSanitizer|LeakSanitizer|MemorySanitizer|ThreadSanitizer):[^\n]*|'
                       r'SUMMARY: (?:AddressSanitizer|LeakSanitizer|MemorySanitizer|ThreadSanitizer):[^\n]*|'
                       r'[^\n]*runtime error:[^\n]*|AddressSanitizer:DEADLYSIGNAL)')
# These diagnostics describe the leak checker, not a detected memory error.
SANITIZER_WARNING = re.compile(
    r'^[^\n]*(?:Running thread \d+ was not suspended\. False leaks are possible\.|'
    r'LeakSanitizer has encountered a fatal error\.)[^\n]*$', re.MULTILINE)
ASSERTION = re.compile(r'Assertion violation|Condition at location [^\n]* violated:')


def sanitizer_messages(stdout, stderr):
    return list(dict.fromkeys(SANITIZER.findall(stdout + '\n' + stderr)))


def sanitizer_warnings(stdout, stderr):
    return list(dict.fromkeys(SANITIZER_WARNING.findall(stdout + '\n' + stderr)))


def combine(semantic_outcome, semantic_reason, sanitizers, errors, timed_out, warnings=()):
    actual = [e for e in errors if e['kind'] not in ('invalid-xml', 'missing-xml')]
    if sanitizers or actual:
        memory = 'fail'
    elif errors or timed_out or warnings:
        memory = 'inconclusive'
    else:
        memory = 'pass'
    if memory == 'fail':
        reason = 'sanitizer reported errors' if sanitizers else 'Valgrind reported errors'
        if warnings: reason += '; leak check needs confirmation'
        return 'fail', reason, memory
    if semantic_outcome == 'fail': return semantic_outcome, semantic_reason, memory
    if memory == 'inconclusive':
        reason = 'sanitizer could not check all threads or complete leak checking' if warnings else 'incomplete memory diagnostics'
        return 'inconclusive', semantic_reason or reason, memory
    return semantic_outcome, semantic_reason, memory
