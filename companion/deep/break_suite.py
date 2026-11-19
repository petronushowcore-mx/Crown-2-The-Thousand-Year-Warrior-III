"""Isolated causal mutations and equivalent transformations of the finite suite.

Every case runs the entire quick population; under --full-only only the two baselines run, on the
enlarged population. A control that names a work also runs that
work directly on the same change: the equivalent must pass with exactly the declared
names of the work, and the damaging change must be refused before any family runs.
Exceptions, absent results, a changed population, stale source hashes and a different
first failure are not detections. This measures the named mutations; it does not
establish semantic completeness.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

SOURCE_NAMES = ('relations.py', 'suite.py', 'map.json')


class RejectedResult(ValueError):
    """Keep the child's primary evidence even when its report is inadmissible."""
    def __init__(self, reason, result, execution):
        super().__init__(reason)
        self.result = result
        self.execution = dict(returncode=execution.returncode, stdout=execution.stdout, stderr=execution.stderr)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_result(result, returncode, population, sources, first=None, profile='quick', work='all'):
    """Validate a full result against externally supplied population and bytes."""
    if result.get('sources') != sources:
        raise ValueError('SOURCE_BINDING')
    if result.get('profile') != profile or result.get('work') != work:
        raise ValueError('EXECUTION_SCOPE')
    rows = result.get('rows', [])
    if not population or [r.get('name') for r in rows] != population:
        raise ValueError('EXACT_POPULATION')
    if any(r.get('status') not in ('PASS', 'FAIL') for r in rows):
        raise ValueError('EXECUTION_ERROR')
    if any(type(r.get('observations')) is not int or r['observations'] <= 0 for r in rows):
        raise ValueError('EMPTY_OBSERVATIONS')
    failures = [r['name'] for r in rows if r['status'] == 'FAIL']
    expected_status, expected_rc = ('FAIL', 1) if failures else ('PASS', 0)
    if result.get('status') != expected_status or returncode != expected_rc:
        raise ValueError('STATUS_RETURN_CODE')
    actual_first = failures[0] if failures else None
    if actual_first != first:
        raise ValueError('FIRST_FAILURE: expected '+repr(first)+'; got '+repr(actual_first))
    if failures and not all(r.get('counterexample') for r in rows if r['status'] == 'FAIL'):
        raise ValueError('MISSING_COUNTEREXAMPLE')
    if not failures and not result.get('relationship_map'):
        raise ValueError('MISSING_RELATION_RESULT')
    return actual_first


def validate_refusal(result, returncode, sources, work):
    """A direct run of one work whose selection differs from its declared name set refuses
    before any family runs, and for that reason, not for another."""
    if result.get('sources') != sources:
        raise ValueError('SOURCE_BINDING')
    if result.get('status') != 'ERROR' or returncode != 1:
        raise ValueError('DIRECT_WORK_NOT_REFUSED')
    if result.get('rows') != []:
        raise ValueError('DIRECT_WORK_RAN_FAMILIES')
    if not str(result.get('error', '')).startswith('ValueError: WORK_SELECTION_MISMATCH: ' + work + ';'):
        raise ValueError('DIRECT_WORK_WRONG_REFUSAL')


def validate_cases(catalogue, population, originals):
    if catalogue.get('schema') != 1:
        raise ValueError('MUTATION_SCHEMA')
    cases = catalogue['mutations']
    if [c['marker'] for c in cases] != population:
        raise ValueError('MUTATION_POPULATION')
    controls = catalogue['controls']
    if not controls or len({c['id'] for c in controls}) != len(controls):
        raise ValueError('CONTROL_POPULATION')
    for case in cases + controls:
        if case['file'] not in ('relations.py', 'suite.py') or case['marker'] not in population:
            raise ValueError('MUTATION_TARGET')
        if not case['old'] or originals[case['file']].count(case['old']) != 1:
            raise ValueError('MUTATION_ANCHOR: '+case.get('id', case['marker']))
        if case['old'] == case['new'] or not case['fact']:
            raise ValueError('IDENTITY_MUTATION_OR_UNNAMED_FACT')
        if 'reach' in case and case['reach'] in (case['old'], case['new']):
            raise ValueError('CONTROL_WITHOUT_DISTINCT_BREAK')
    works = json.loads(originals['map.json']).get('work_checks', {})
    for case in cases + controls:
        if 'work' in case and ('reach' not in case or case['work'] not in works):
            raise ValueError('DIRECT_WORK_TARGET: '+case.get('id', case['marker']))


def judge_checks():
    """Known good reports and one-fact corruptions of the result contract."""
    sources = {'a.py': 'example-source'}
    good = dict(sources=sources, profile='quick', work='all', status='PASS',
                rows=[dict(name='a', status='PASS', observations=1),
                      dict(name='b', status='PASS', observations=1)],
                relationship_map=[{'id': 'computed'}])
    seen = []
    def accepts(name, result, rc, first=None):
        validate_result(result, rc, ['a', 'b'], sources, first)
        seen.append(name)
    def refused(name, call, reason):
        try:
            call()
        except ValueError as exc:
            if not str(exc).startswith(reason):
                raise ValueError(name+': wrong refusal '+str(exc)) from exc
            seen.append(name)
            return
        raise ValueError(name+': accepted broken report')
    def refuses(name, result, rc, reason, first=None, expected_sources=sources):
        refused(name, lambda: validate_result(result, rc, ['a', 'b'], expected_sources, first), reason)
    accepts('honest-pass', good, 0)
    bad = copy.deepcopy(good)
    bad['status'] = 'FAIL'
    bad['rows'][1].update(status='FAIL', counterexample='named counterexample')
    accepts('honest-first-failure', bad, 1, 'b')
    refuses('wrong-first-failure', bad, 1, 'FIRST_FAILURE', 'a')
    refuses('false-success-code', bad, 0, 'STATUS_RETURN_CODE', 'b')
    refuses('nonzero-honest-code', good, 1, 'STATUS_RETURN_CODE')
    for kind, change, reason in (
        ('missing-row', lambda x:x['rows'].pop(), 'EXACT_POPULATION'),
        ('duplicate-row', lambda x:x['rows'].append(x['rows'][0]), 'EXACT_POPULATION'),
        ('reordered-rows', lambda x:x['rows'].reverse(), 'EXACT_POPULATION'),
        ('unknown-row', lambda x:x['rows'][0].update(name='unknown'), 'EXACT_POPULATION'),
        ('technical-error', lambda x:x['rows'][0].update(status='ERROR'), 'EXECUTION_ERROR'),
        ('unknown-status', lambda x:x['rows'][0].update(status='SKIP'), 'EXECUTION_ERROR'),
        ('empty-observations', lambda x:x['rows'][0].update(observations=0), 'EMPTY_OBSERVATIONS'),
        ('boolean-observations', lambda x:x['rows'][0].update(observations=True), 'EMPTY_OBSERVATIONS'),
        ('stale-source', lambda x:x['sources'].update(other='bytes'), 'SOURCE_BINDING'),
        ('wrong-scope', lambda x:x.update(work='body'), 'EXECUTION_SCOPE'),
        ('wrong-profile', lambda x:x.update(profile='full'), 'EXECUTION_SCOPE'),
        ('false-overall-status', lambda x:x.update(status='FAIL'), 'STATUS_RETURN_CODE'),
        ('missing-composition', lambda x:x.update(relationship_map=[]), 'MISSING_RELATION_RESULT'),
    ):
        broken = copy.deepcopy(good)
        change(broken)
        refuses(kind, broken, 0, reason)
    missing = copy.deepcopy(bad)
    missing['rows'][1].pop('counterexample')
    refuses('missing-counterexample', missing, 1, 'MISSING_COUNTEREXAMPLE', 'b')
    # A direct run of one work is judged under its own scope; a refusal counts only when it
    # names a selection that differs from the declared set of that work.
    direct = dict(copy.deepcopy(good), work='warrior')
    validate_result(direct, 0, ['a', 'b'], sources, None, 'quick', 'warrior')
    seen.append('honest-direct-work')
    refused('all-run-as-direct-work', lambda: validate_result(good, 0, ['a', 'b'], sources, None, 'quick', 'warrior'), 'EXECUTION_SCOPE')
    refusal = dict(sources=sources, status='ERROR', rows=[],
                   error="ValueError: WORK_SELECTION_MISMATCH: warrior; missing ['t_W01']; extra []; selected 1 of 2 declared")
    validate_refusal(refusal, 1, sources, 'warrior')
    seen.append('honest-refusal')
    for kind, report, rc, work, reason in (
        ('pass-as-refusal', direct, 0, 'warrior', 'DIRECT_WORK_NOT_REFUSED'),
        ('refusal-success-code', refusal, 0, 'warrior', 'DIRECT_WORK_NOT_REFUSED'),
        ('refusal-after-rows', dict(refusal, rows=good['rows']), 1, 'warrior', 'DIRECT_WORK_RAN_FAMILIES'),
        ('refusal-other-reason', dict(refusal, error='ValueError: unknown map schema or missing scope'), 1, 'warrior', 'DIRECT_WORK_WRONG_REFUSAL'),
        ('refusal-other-work', refusal, 1, 'body', 'DIRECT_WORK_WRONG_REFUSAL'),
        ('refusal-stale-source', dict(refusal, sources={'a.py': 'other'}), 1, 'warrior', 'SOURCE_BINDING'),
    ):
        refused(kind, lambda: validate_refusal(report, rc, sources, work), reason)
    return seen


def scientific_payload(result):
    return {k:v for k,v in result.items() if k != 'sources'}


def run_case(base, originals, population, identity, change=None, first=None, optimized=False, timeout=120, profile='quick', work='all', refusal=False):
    with tempfile.TemporaryDirectory(prefix='triad-'+identity+'-') as temporary:
        folder = Path(temporary)
        for name in SOURCE_NAMES:
            shutil.copyfile(base/name, folder/name)
        if change is not None:
            file, old, new = change
            (folder/file).write_text(originals[file].replace(old,new,1),encoding='utf-8')
        sources = {name:sha(folder/name) for name in SOURCE_NAMES}
        argv = [sys.executable, '-B'] + (['-O'] if optimized else [])
        argv += [str(folder/'suite.py'), '--teeth', '--profile', profile, '--work', work, '--json', str(folder/'result.json')]
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
        executed = subprocess.run(argv, cwd=folder, env=env, capture_output=True, text=True,
                                  encoding='utf-8', timeout=timeout)
        result_path = folder/'result.json'
        if not result_path.is_file():
            raise ValueError('NO_RESULT: '+executed.stderr[-2000:])
        result = json.loads(result_path.read_text(encoding='utf-8'))
        try:
            if refusal:
                validate_refusal(result,executed.returncode,sources,work)
            else:
                validate_result(result,executed.returncode,population,sources,first,profile,work)
        except ValueError as exc:
            raise RejectedResult(str(exc), result, executed) from exc
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--json', default='mutation-result.json')
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--full-only', action='store_true', help='compare the enlarged population in normal and optimized Python; mutations remain a separate quick run')
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    originals = {name:(base/name).read_text(encoding='utf-8') for name in SOURCE_NAMES}
    mapping = json.loads(originals['map.json'])
    population = [row['check'] for row in mapping['checks']]
    catalogue = json.loads((base/'mutations.json').read_text(encoding='utf-8'))
    validate_cases(catalogue,population,originals)
    profile = 'full' if args.full_only else 'quick'
    report = dict(status='RUNNING', cases=[], active=None, judge_checks=judge_checks(),
                  sources={name:sha(base/name) for name in SOURCE_NAMES+('mutations.json','break_suite.py')},
                  scope=('Enlarged finite population in normal and optimized Python' if args.full_only else 'Named causal mutations on the full quick population, and a direct run of the work a control names')+'; no universal coverage claim')
    output = Path(args.json)
    def save():
        output.write_text(json.dumps(report,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    baseline = None
    tasks = [('baseline',None,None,False,None),('optimized',None,None,True,None)]
    tasks += [] if args.full_only else [(c['marker'],(c['file'],c['old'],c['new']),c['marker'],False,None) for c in catalogue['mutations']]
    for control in (() if args.full_only else catalogue['controls']):
        # A control naming a work also runs that work directly on the same change: the
        # equivalent must pass with exactly the declared names of the work, in map order;
        # the damaging change must be refused before any family runs.
        work = control.get('work')
        declared = [name for name in population if name in mapping['work_checks'][work]] if work else None
        tasks.append(('equivalent-'+control['id'],(control['file'],control['old'],control['new']),None,False,(work,False,declared) if work else None))
        tasks.append(('reach-'+control['id'],(control['file'],control['old'],control['reach']),control['marker'],False,(work,True,None) if work else None))
    for identity,change,first,optimized,direct in tasks:
        report['active'] = identity
        save()
        row = dict(id=identity, expected_first=first, status='PASS')
        try:
            result = run_case(base,originals,population,identity,change,first,optimized,args.timeout,profile)
            row['result'] = result
            if identity == 'baseline':
                baseline = scientific_payload(result)
            elif first is None and scientific_payload(result) != baseline:
                raise ValueError('SCIENTIFIC_RESULT_CHANGED_ON_EQUIVALENCE')
            if direct is not None:
                work, refusal, declared = direct
                try:
                    row['direct'] = run_case(base,originals,declared,identity+'-'+work,change,None,False,args.timeout,profile,work,refusal)
                except RejectedResult as exc:
                    row.update(direct=exc.result, direct_execution=exc.execution)
                    raise ValueError('DIRECT_WORK '+work+': '+str(exc)) from exc
        except Exception as exc:
            row.update(status='FAIL',error=type(exc).__name__+': '+str(exc))
            if isinstance(exc, RejectedResult):
                row.update(result=exc.result, execution=exc.execution)
        report['cases'].append(row)
        save()
        if row['status'] != 'PASS':
            print('FAIL '+identity+': '+row['error'],flush=True)
        if identity == 'baseline' and row['status'] != 'PASS':
            break
    report['active'] = None
    report['status'] = 'PASS' if len(report['cases'])==len(tasks) and all(r['status']=='PASS' for r in report['cases']) else 'FAIL'
    save()
    count = sum(r['status']=='PASS' for r in report['cases'])
    print(('full population: ' if args.full_only else 'mutations and controls: ')+str(count)+'/'+str(len(tasks))+'; '+report['status'])
    return 0 if report['status']=='PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
