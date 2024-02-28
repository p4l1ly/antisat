import sys

flags0 = {
    "afa": (
        ([], None, [["afa"]]),
        ([], None, [["trie"], ["clause"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_HEAP"), [["heap1", "heap2", "anyHeap"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_BUBBLE"), [["heap1", "bubble2", "anyHeap", "anyBubble"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_WATCH"), [["heap1", "watch2", "anyHeap", "anyWatch"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_HEAP"), [["bubble1", "heap2", "anyHeap", "anyBubble"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_WATCH"), [["bubble1", "watch2", "anyBubble", "anyWatch"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_HEAP"), [["watch1", "heap2", "anyWatch", "anyHeap"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_BUBBLE"), [["watch1", "bubble2", "anyWatch", "anyBubble"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_WATCH"), [["watch1", "watch2", "anyWatch"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_HEAP"), [["heap1", "heap2", "anyHeap"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_BUBBLE"), [["heap1", "bubble2", "anyHeap", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_WATCH"), [["heap1", "watch2", "anyHeap", "anyWatch"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_HEAP"), [["bubble1", "heap2", "anyHeap", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_WATCH"), [["bubble1", "watch2", "anyBubble", "anyWatch"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_HEAP"), [["watch1", "heap2", "anyWatch", "anyHeap"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_BUBBLE"), [["watch1", "bubble2", "anyWatch", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_WATCH"), [["watch1", "watch2", "anyWatch"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        # ([], ("NEW_ANALYZE", "ON"), [["newAnalyze"]]),
        # ([], ("STRENGTHENCC", "OFF"), [["noStrengthencc"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
        # (["afa", "outputs"], ("NO_POSNEG_OUTPUTS", "OFF"), [["posnegOutputs"]]),
        (["afa"], ("NO_POSNEG_OUTPUTS", "ON"), [["noPosnegOutputs"]]),
        (["afa"], ("ONE_ORDER", "OFF"), [["twoOrders"]]),
        # (["afa"], ("ONE_ORDER", "ON"), [["oneOrder"]]),
        (["afa"], ("NO_OUTPUTS", "OFF"), [["outputs"]]),
        # (["afa", "oneOrder"], ("NO_OUTPUTS", "ON"), [["noOutputs"]]),
        (["afa"], ("CELL_CONTAINER", "DFS"), [["dfs"]]),
        (["afa"], ("CELL_CONTAINER", "BFS"), [["bfs"]]),
        (["afa"], ("CELL_CONTAINER", "SET"), [["set"]]),
        # (["afa"], ("NOGUESS_VARS", "OFF"), [["noNoguessVars"]]),
        (["afa"], ("NOGUESS_VARS", "ON"), [["noguessVars"]]),
        # (["afa", "noguessVars", "outputs"], ("POSQ_OUTPUTS", "OFF"), [["noPosqOutputs"]]),
        (["afa", "noguessVars", "outputs"], ("POSQ_OUTPUTS", "ON"), [["posqOutputs"]]),
        (["afa"], ("OPTIONAL_CLAUSES", "OFF"), [["noOptionalClauses"]]),
        (["afa"], ("OPTIONAL_CLAUSES", "ON"), [["optionalClauses"]]),
        (["afa", "optionalClauses"], ("UPWARD_CLAUSES", "OFF"), [["noUpwardClauses"]]),
        (["afa", "optionalClauses"], ("UPWARD_CLAUSES", "ON"), [["upwardClauses"]]),
    ),
    "afa_small": (
        ([], None, [["afa"]]),
        ([], None, [["trie"], ["clause"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_BUBBLE"), [["watch1", "bubble2", "anyWatch", "anyBubble"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        (["afa"], ("NO_POSNEG_OUTPUTS", "ON"), [["noPosnegOutputs"]]),
        (["afa"], ("ONE_ORDER", "OFF"), [["twoOrders"]]),
        (["afa"], ("NO_OUTPUTS", "OFF"), [["outputs"]]),
        (["afa"], ("CELL_CONTAINER", "SET"), [["set"]]),
        (["afa"], ("NOGUESS_VARS", "ON"), [["noguessVars"]]),
        (["afa", "noguessVars", "outputs"], ("POSQ_OUTPUTS", "ON"), [["posqOutputs"]]),
        (["afa"], ("OPTIONAL_CLAUSES", "ON"), [["optionalClauses"]]),
        (["afa", "optionalClauses"], ("UPWARD_CLAUSES", "OFF"), [["noUpwardClauses"]]),
        (["afa", "optionalClauses", "trie", "bubble1", "noAllSolo"], ("UPWARD_CLAUSES", "ON"), [["upwardClauses"]]),
    ),
    "afa_tiny": (
        ([], None, [["afa"]]),
        (["afa"], ("NO_POSNEG_OUTPUTS", "ON"), [["noPosnegOutputs"]]),
        (["afa"], ("ONE_ORDER", "OFF"), [["twoOrders"]]),
        (["afa"], ("NO_OUTPUTS", "OFF"), [["outputs"]]),
        (["afa"], ("CELL_CONTAINER", "SET"), [["set"]]),
        (["afa"], ("NOGUESS_VARS", "OFF"), [["noNoguessVars"]]),
        (["afa"], ("NOGUESS_VARS", "ON"), [["noguessVars"]]),
        (["afa", "noguessVars", "outputs"], ("POSQ_OUTPUTS", "ON"), [["posqOutputs"]]),
        (["afa", "noguessVars"], ("OPTIONAL_CLAUSES", "OFF"), [["noOptionalClauses"]]),
        (["afa"], ("OPTIONAL_CLAUSES", "ON"), [["optionalClauses"]]),
        (["afa", "optionalClauses", "noguessVars"], ("UPWARD_CLAUSES", "OFF"), [["noUpwardClauses"]]),
        (["afa", "optionalClauses"], ("UPWARD_CLAUSES", "ON"), [["upwardClauses"]]),
        (["upwardClauses", "optionalClauses", "noguessVars"], None, [["trie"], ["clause"]]),
        (["noOptionalClauses"], None, [["trie"]]),
        (["optionalClauses", "noUpwardClauses"], None, [["trie"]]),
        (["optionalClauses", "upwardClauses", "noNoguessVars"], None, [["trie"]]),
        (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_BUBBLE"), [["bubble1", "bubble2", "anyBubble"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie", "upwardClauses", "optionalClauses", "noguessVars"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
    ),
    "sat_clause": (
        ([], None, [["sat"]]),
        ([], None, [["clause"]]),
        (["sat", "clause"], ("MODE", "SAT_CLAUSE_HEAP"), [["anyHeap"]]),
        (["sat", "clause"], ("MODE", "SAT_CLAUSE_BUBBLE"), [["anyBubble"]]),
        (["sat", "clause"], ("MODE", "SAT_CLAUSE_WATCH"), [["anyWatch"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        # ([], ("NEW_ANALYZE", "ON"), [["newAnalyze"]]),
        ([], ("STRENGTHENCC", "OFF"), [["noStrengthencc"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
    ),
    "sat_trie": (
        ([], None, [["sat"]]),
        ([], None, [["trie"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_HEAP"), [["anyHeap"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_BUBBLE"), [["anyBubble"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_WATCH"), [["anyWatch"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        # ([], ("NEW_ANALYZE", "ON"), [["newAnalyze"]]),
        ([], ("STRENGTHENCC", "OFF"), [["noStrengthencc"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        # (["sat", "trie"], ("SOLIDIFY", "OFF"), [["noSolidify"]]),
        (["sat", "trie"], ("SOLIDIFY", "ON"), [["solidify"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["sat", "trie"], ("FIXED_ORDER", "OFF"), [["noFixedOrder"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
    ),
    "sat_trie_fixed": (
        ([], None, [["sat"]]),
        ([], None, [["trie"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_HEAP"), [["anyHeap"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_BUBBLE"), [["anyBubble"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_WATCH"), [["anyWatch"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        # ([], ("NEW_ANALYZE", "ON"), [["newAnalyze"]]),
        ([], ("STRENGTHENCC", "OFF"), [["noStrengthencc"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        # (["sat", "trie"], ("SOLIDIFY", "OFF"), [["noSolidify"]]),
        (["sat", "trie"], ("SOLIDIFY", "ON"), [["solidify"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["sat", "trie"], ("FIXED_ORDER", "ON"), [["fixedOrder"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
    ),
    "sat_small": (
        ([], None, [["sat"]]),
        ([], None, [["trie"], ["clause"]]),
        (["sat", "clause"], ("MODE", "SAT_CLAUSE_BUBBLE"), [["anyBubble"]]),
        (["sat", "trie"], ("MODE", "SAT_TRIE_BUBBLE"), [["anyBubble"]]),
        ([], ("NEW_ANALYZE", "OFF"), [["oldAnalyze"]]),
        ([], ("STRENGTHENCC", "ON"), [["strengthencc"]]),
        (["sat", "trie"], ("SOLIDIFY", "ON"), [["solidify"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["sat", "trie"], ("FIXED_ORDER", "ON"), [["fixedOrder"]]),
    ),
}[sys.argv[2]]

suffix = {
    "afa": "",
    "afa_small": "s",
    "afa_tiny": "afa_tiny",
    "sat_clause": "sat",
    "sat_trie": "satt",
    "sat_trie_fixed": "satf",
    "sat_small": "sats",
}[sys.argv[2]]

visited = set()
results = []

def recur(
    flags_mustnot: tuple,
    flags: tuple,
    options_set: frozenset,
    options: tuple,
    settings_keys: frozenset,
    settings: tuple,
):
    assert (options, settings_keys, settings) not in visited
    visited.add((options, settings_keys, settings))

    found_continuation = False
    for i, flag in enumerate(flags):
        conditions, new_setting, new_options = flag
        if not all(cond in options_set for cond in conditions):
            continue

        if new_setting is not None:
            if new_setting[0] in settings_keys:
                continue

            settings2 = settings + (f"-D{new_setting[0]}={new_setting[1]}",)
            settings2_keys = settings_keys | frozenset((new_setting[0],))
        else:
            settings2 = settings
            settings2_keys = settings_keys

        flags2 = flags[i + 1:]

        for new_option in new_options:
            if new_option:
                options2 = options + tuple(new_option)
                options2_set = options_set | frozenset(new_option)
            else:
                options2 = options
                options2_set = options_set

            recur(flags_mustnot, flags2, options2_set, options2, settings2_keys, settings2)
            found_continuation = True

        flags_mustnot = flags_mustnot + (flag,)

    if not found_continuation:
        for flag in flags_mustnot:
            conditions, new_setting, new_options = flag
            if not all(cond in options_set for cond in conditions):
                continue

            if new_setting is not None:
                if new_setting[0] in settings_keys:
                    continue

            return
        results.append((settings, options))

recur((), flags0, frozenset(), (), frozenset(), ())

results_set = set(r[0] for r in results)
assert len(results_set) == len(results)
results_set = set(r[1] for r in results)
if len(results_set) != len(results):
    results_set = set()
    for r in results:
        if r[1] in results_set:
            print(r[1])
        results_set.add(r[1])
    raise Exception("Duplicate results")

if sys.argv[1] == "build_script":
    for i, (result, _) in enumerate(results):
        print(f"cmake -DCMAKE_BUILD_TYPE=Release -S . -B build{suffix}{i}", *result)

    for i, _ in enumerate(results):
        print(f"cmake --build build{suffix}{i}")
elif sys.argv[1] == "tags":
    for i, (_, result) in enumerate(results):
        print(f"build{suffix}{i}", *result)
