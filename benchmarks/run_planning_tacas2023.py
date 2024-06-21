import time 
import subprocess
from subprocess import TimeoutExpired

instances = [ 
        # ==================== SP ====================
        {
            'name': 'SP 10x10',
            'systems': ['./planning_tacas2023/robotic_sp_100.smv'],
            'formula': './planning_tacas2023/robotic_sp_formula.hq'
        },
        {
            'name': 'SP 20x20',
            'systems': ['./planning_tacas2023/robotic_sp_400.smv'],
            'formula': './planning_tacas2023/robotic_sp_formula.hq'
        },
        {
            'name': 'SP 40x40',
            'systems': ['./planning_tacas2023/robotic_sp_1600.smv'],
            'formula': './planning_tacas2023/robotic_sp_formula.hq'
        },
        {
            'name': 'SP 60x60',
            'systems': ['./planning_tacas2023/robotic_sp_3600.smv'],
            'formula': './planning_tacas2023/robotic_sp_formula.hq'
        },
        # ==================== RP ====================
        {
            'name': 'RP 10x10',
            'systems': ['./planning_tacas2023/robotic_robustness_100.smv'],
            'formula': './planning_tacas2023/robotic_robustness_formula.hq'
        },
        {
            'name': 'RP 20x20',
            'systems': ['./planning_tacas2023/robotic_robustness_400.smv'],
            'formula': './planning_tacas2023/robotic_robustness_formula.hq'
        },
        {
            'name': 'RP 40x40',
            'systems': ['./planning_tacas2023/robotic_robustness_1600.smv'],
            'formula': './planning_tacas2023/robotic_robustness_formula.hq'
        },
        {
            'name': 'RP 60x60',
            'systems': ['./planning_tacas2023/robotic_robustness_3600.smv'],
            'formula': './planning_tacas2023/robotic_robustness_formula.hq'
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

    # args = ["--nusmv", '--no-bisim', '--incl-rabit'] + sys + [prop]
    # args = ["--nusmv", '--no-bisim', '--incl-bait'] + sys + [prop]
    # args = ["--nusmv", '--no-bisim', '--incl-forklift'] + sys + [prop]
    # args = ["--nusmv", '--no-bisim', '--incl-forq'] + sys + [prop]
    args = ["--nusmv", '--no-bisim', '--incl-spot'] + sys + [prop]

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
