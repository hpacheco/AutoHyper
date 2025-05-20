import spot
import argparse

parser = argparse.ArgumentParser(description="Convert HOA to Explicit State")

parser.add_argument("-i", "--input", required=True, help="Input file *.hoa")
parser.add_argument("-o", "--output", required=True, help="Output file *.exp")

args = parser.parse_args()

automaton = spot.automaton(args.input)

bdd_dict = automaton.get_dict()

#acc_cond = automaton.get_acceptance()
#print("Acceptance condition:", acc_cond)

aps = automaton.ap()
#print(aps)

start_state = automaton.get_init_state_number()
#print(start_state)

def extract_dnf_from_formula(formula):
    
    if formula.kind() == spot.op_Or:
        return [extract_ands_from_formula(term) for term in formula]
    elif formula.kind() == spot.op_And:
        return [extract_ands_from_formula(formula)]
    else: raise Exception("not DNF formula {str(formula)}")

def extract_ands_from_formula(formula):
    vs = []
    for term in formula:
        if term.kind() == spot.op_Not:
            v = term[0]
            if v.kindstr() == "ap":
                vs.append((str(v),False))
            else: raise Exception("not an atom {str(v)}")
        elif term.kindstr() == "ap":
            vs.append((str(term),True))
        else: raise Exception("not a conjunct {str(term)}")
    return vs

def renderBool(b):
    if b: return "true"
    else: return "false"

def renderExplicitState(conj):
    s = ""
    for (var,val) in conj:
        s += " (\"" + var + "\" " + renderBool(val) + ")"
    return "{" + s[1:] + "}"

parsedStates = {}
numOutConds = 0
outConds = {}

for state in range(automaton.num_states()):
    outs = {}
    for edge in automaton.out(state):
        num_acc_sets = edge.acc.count()
        if num_acc_sets: print("acceptance sets not supported {edge.acc}")
        formula = spot.bdd_to_formula(edge.cond,bdd_dict)
        dnf = extract_dnf_from_formula(formula)
        for trans_cond in dnf:
            trans_str = renderExplicitState(trans_cond)
            if trans_str not in outConds:
                outConds[trans_str] = numOutConds
                numOutConds += 1
            if trans_str in outs: outs[trans_str].add(edge.dst)
            else: outs[trans_str] = {edge.dst}
    parsedStates[state] = outs

#print(parsedStates)
#print(numOutConds)
#print(outConds)

outStates = {}

def resolveDests(dests):
    r = set()
    for dest in dests:
        for c in parsedStates[dest].keys():
            r.add(outConds[c])
    return r

for state,trans in parsedStates.items():
    for cond,dests in trans.items():
        if cond in outStates:
            outStates[cond].update(resolveDests(dests))
        else:
            outStates[cond] = resolveDests(dests)

#print(outStates)

def showNums(outNums):
    dests = ""
    for outNum in outNums:
        dests += str(outNum) + " "
    return dests

with open(args.output, "w") as f:
    vs = ""
    for ap in aps:
        vs += " (\"" + str(ap) + "\" Bool)"
    print(f"Variables:{vs}",file=f)
    inits = showNums({ outConds[s] for s in parsedStates[start_state].keys() })
    print(f"Init: {inits}",file=f)
    print("--BODY--",file=f)
    for inState,outNums in outStates.items():
        inNum = outConds[inState]
        print(f"State: {inNum} {inState}",file=f)
        print(showNums(outNums),file=f)
    print("--END--",file=f)

