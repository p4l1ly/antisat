import sys

flags0 = {
    "afa": [
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
    ],
    "sat_clause": [
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
    ],
    "sat_trie": [
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
        (["sat", "trie"], ("SOLIDIFY", "ON"), [["solidfy"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["trie"], ("FIXED_ORDER", "OFF"), [["noFixedOrder"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
    ],
    "sat_trie_fixed": [
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
        (["sat", "trie"], ("SOLIDIFY", "ON"), [["solidfy"]]),
        (["trie"], ("ALL_SOLO", "OFF"), [["noAllSolo"]]),
        (["trie"], ("ALL_SOLO", "ON"), [["allSolo"]]),
        (["trie"], ("FIXED_ORDER", "ON"), [["fixedOrder"]]),
        (["anyWatch"], ("WATCH_LEARNT_WATCH", "OFF"), [["noWatchLearntWatch"]]),
        # (["anyWatch"], ("WATCH_LEARNT_WATCH", "ON"), [["watchLearntWatch"]]),
    ]
}[sys.argv[2]]

suffix = {
    "afa": "",
    "sat_clause": "sat",
    "sat_trie": "satt",
    "sat_trie_fixed": "satf",
}[sys.argv[2]]

visited = set()
results = []

def recur(flags, options: frozenset, settings_keys: frozenset, settings: frozenset):
    if (options, settings_keys, settings) in visited:
        # print("VISITED")
        return frozenset()
    # print((options, settings_keys, settings))
    visited.add((options, settings_keys, settings))

    found_continuation = False
    for flag in flags:
        conditions, new_setting, new_options = flag
        if not all(cond in options for cond in conditions):
            continue

        if new_setting is not None:
            if new_setting[0] in settings_keys:
                continue

            settings2 = settings | frozenset((f"-D{new_setting[0]}={new_setting[1]}",))
            settings2_keys = settings_keys | frozenset((new_setting[0],))
        else:
            settings2 = settings
            settings2_keys = settings_keys

        flags2 = flags.copy()
        flags2.remove(flag)

        for new_option in new_options:
            if new_option:
                options2 = options | frozenset(new_option)
            else:
                options2 = options

            recur(flags2, options2, settings2_keys, settings2)
            found_continuation = True

    if not found_continuation:
        results.append((tuple(sorted(settings)), tuple(sorted(options))))

recur(flags0, frozenset(), frozenset(), frozenset())

if len(sys.argv) > 3:
    order = {}
    with open(sys.argv[3], "r") as f:
        for line in f:
            order[tuple(sorted(line.strip().split()[6:]))] = len(order)
    results2 = [0] * len(results)
    for (result, tags) in results:
        results2[order[result]] = result, tags
    results = results2
else:
    results.sort()

results_set = set(r[0] for r in results)
assert len(results_set) == len(results)
results_set = set(r[1] for r in results)
assert len(results_set) == len(results)

if sys.argv[1] == "build_script":
    for i, (result, _) in enumerate(results):
        print(f"cmake -DCMAKE_BUILD_TYPE=Release -S . -B build{suffix}{i}", *sorted(result))

    for i, _ in enumerate(results):
        print(f"cmake --build build{suffix}{i}")
elif sys.argv[1] == "tags":
    for i, (_, result) in enumerate(results):
        print(f"build{suffix}{i}", *sorted(result))
