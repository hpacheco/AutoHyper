import time 
import subprocess
from subprocess import TimeoutExpired

instances = [
        # ==================== Bakery ====================
        {
            'name': 'Bakery_3, S1',
            'systems': ['./symbolic_tacas2023/bakery/bakery_3procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_S1_3proc.hq'
        },
        {
            'name': 'Bakery_3, S2',
            'systems': ['./symbolic_tacas2023/bakery/bakery_3procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_S2_3proc.hq'
        },
        {
            'name': 'Bakery_3, S3',
            'systems': ['./symbolic_tacas2023/bakery/bakery_3procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_S3_3proc.hq'
        },
        {
            'name': 'Bakery_3, sym_1',
            'systems': ['./symbolic_tacas2023/bakery/bakery_3procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_sym1_3proc.hq'
        },
        {
            'name': 'Bakery_3, sym_2',
            'systems': ['./symbolic_tacas2023/bakery/bakery_3procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_sym2_3proc.hq'
        },
        {
            'name': 'Bakery_5, sym_1',
            'systems': ['./symbolic_tacas2023/bakery/bakery_5procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_sym1_5proc.hq'
        },
        {
            'name': 'Bakery_5, sym_2',
            'systems': ['./symbolic_tacas2023/bakery/bakery_5procs.smv'],
            'formula': './symbolic_tacas2023/bakery/bakery_formula_sym2_5proc.hq'
        },
        # ==================== SNARK ====================
        {
            'name': 'SNARK-Bug1, lin',
            'systems': ['./symbolic_tacas2023/snark/snark1_M1_concurrent.smv', './symbolic_tacas2023/snark/snark1_M2_sequential.smv'],
            'formula': './symbolic_tacas2023/snark/snark1_formula.hq'
        },
        # ==================== NI ====================
        {
            'name': '3-Thread_correct, ni',
            'systems': ['./symbolic_tacas2023/ni/NI_correct.smv'],
            'formula': './symbolic_tacas2023/ni/NI_formula.hq'
        },
        {
            'name': '3-Thread_incorrect, ni',
            'systems': ['./symbolic_tacas2023/ni/NI_incorrect.smv'],
            'formula': './symbolic_tacas2023/ni/NI_formula.hq'
        },
        # ==================== NRP ====================
        {
            'name': 'NRP_T_correct, fair',
            'systems': ['./symbolic_tacas2023/nrp/NRP_correct.smv'],
            'formula': './symbolic_tacas2023/nrp/NRP_formula.hq'
        },
        {
            'name': 'NRP_T_incorrect, fair',
            'systems': ['./symbolic_tacas2023/nrp/NRP_incorrect.smv'],
            'formula': './symbolic_tacas2023/nrp/NRP_formula.hq'
        },
        # ==================== Mutation ====================
        {
            'name': 'Mutant, mut',
            'systems': ['./symbolic_tacas2023/mutation/mutation_testing.smv'],
            'formula': './symbolic_tacas2023/mutation/mutation_testing.hq'
        }
    ]


def run_with_timeout(cmd : list[str], timeout_sec=None):
    proc = subprocess.Popen(' '.join(cmd), shell=True, stderr=subprocess.PIPE, stdout=subprocess.PIPE)

    try:
        stdout, stderr = proc.communicate(timeout=timeout_sec)
    except TimeoutExpired:
        proc.kill()
        return None, "", ""
   
    return proc.returncode, stdout.decode("utf-8").strip(), stderr.decode("utf-8").strip()

for i in instances: 
    name = i['name']
    sys = i['systems']
    prop = i['formula']

    print("")
    print("----------------------------------------")
    print("Instance: " + name)

    # args = ["--nusmv", '--incl-bait'] + sys + [prop]
    # args = ["--nusmv", '--incl-rabit'] + sys + [prop]
    # args = ["--nusmv", '--incl-forklift'] + sys + [prop]
    # args = ["--nusmv", '--incl-forq'] + sys + [prop]
    args = ["--nusmv", '--incl-spot'] + sys + [prop]

    startTime = time.time()
    code, stdout, stderr = run_with_timeout(["../app/AutoHyper"] + args, 60)
    endTime = time.time()
    et = endTime - startTime 

    if code == None:
        print("TO")
    else:
        print("\033[94m" + stdout + "\033[0m")
        print("")
        print("Time :", "%.2f" % et, "s")

    print("----------------------------------------")
