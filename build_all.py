flags0 = [
    # ([], None, [["sat"], ["afa"]]),
    ([], None, [["afa"]]),
    ([], None, [["trie"], ["clause"]]),
    # (["sat", "trie"], ("MODE", "SAT_TRIE_HEAP"), [[]]),
    # (["sat", "trie"], ("MODE", "SAT_TRIE_BUBBLE"), [[]]),
    # (["sat", "trie"], ("MODE", "SAT_TRIE_WATCH"), [["watch"]]),
    # (["sat", "clause"], ("MODE", "SAT_CLAUSE_HEAP"), [[]]),
    # (["sat", "clause"], ("MODE", "SAT_CLAUSE_BUBBLE"), [[]]),
    # (["sat", "clause"], ("MODE", "SAT_CLAUSE_WATCH"), [["watch"]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_HEAP"), [[]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_BUBBLE"), [[]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_HEAP_WATCH"), [["watch"]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_HEAP"), [[]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_BUBBLE"), [[]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_BUBBLE_WATCH"), [["watch"]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_HEAP"), [["watch"]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_BUBBLE"), [["watch"]]),
    (["afa", "clause"], ("MODE", "AFA_CLAUSE_WATCH_WATCH"), [["watch"]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_HEAP"), [[]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_BUBBLE"), [[]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_HEAP_WATCH"), [["watch"]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_HEAP"), [[]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_BUBBLE"), [[]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_BUBBLE_WATCH"), [["watch"]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_HEAP"), [["watch"]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_BUBBLE"), [["watch"]]),
    (["afa", "trie"], ("MODE", "AFA_TRIE_WATCH_WATCH"), [["watch"]]),
    # ([], ("NEW_ANALYZE", "OFF"), [[]]),
    ([], ("NEW_ANALYZE", "ON"), [[]]),
    # ([], ("STRENGTHENCC", "OFF"), [[]]),
    ([], ("STRENGTHENCC", "ON"), [[]]),
    # (["sat", "trie"], ("SOLIDIFY", "OFF"), [[]]),
    (["sat", "trie"], ("SOLIDIFY", "ON"), [[]]),
    (["trie"], ("ALL_SOLO", "OFF"), [[]]),
    (["trie"], ("ALL_SOLO", "ON"), [[]]),
    (["watch"], ("WATCH_LEARNT_WATCH", "OFF"), [[]]),
    # (["watch"], ("WATCH_LEARNT_WATCH", "ON"), [[]]),
    # (["afa", "outputs"], ("NO_POSNEG_OUTPUTS", "OFF"), [[]]),
    (["afa"], ("NO_POSNEG_OUTPUTS", "ON"), [[]]),
    (["afa"], ("ONE_ORDER", "OFF"), [[]]),
    # (["afa"], ("ONE_ORDER", "ON"), [["oneorder"]]),
    (["afa"], ("NO_OUTPUTS", "OFF"), [["outputs"]]),
    # (["afa", "oneorder"], ("NO_OUTPUTS", "ON"), [[]]),
    (["afa"], ("CELL_CONTAINER", "DFS"), [[]]),
    (["afa"], ("CELL_CONTAINER", "BFS"), [[]]),
    (["afa"], ("CELL_CONTAINER", "SET"), [[]]),
    # (["afa"], ("NOGUESS_VARS", "OFF"), [[]]),
    (["afa"], ("NOGUESS_VARS", "ON"), [["noguess_vars"]]),
    # (["afa", "noguess_vars", "outputs"], ("POSQ_OUTPUTS", "OFF"), [[]]),
    (["afa", "noguess_vars", "outputs"], ("POSQ_OUTPUTS", "ON"), [[]]),
    (["afa"], ("OPTIONAL_CLAUSES", "OFF"), [[]]),
    (["afa"], ("OPTIONAL_CLAUSES", "ON"), [["optional_clauses"]]),
    (["afa", "optional_clauses"], ("UPWARD_CLAUSES", "OFF"), [[]]),
    (["afa", "optional_clauses"], ("UPWARD_CLAUSES", "ON"), [[]]),
]

visited = set()
results = set()

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
        if settings == frozenset(("-DNEW_ANALYZE=ON", "-DSTRENGTHENCC=ON")):
            print("HEY ", options, flags, settings_keys)
        results.add(settings)

recur(flags0, frozenset(), frozenset(), frozenset())

for i, result in enumerate(results):
    print(f"cmake -DCMAKE_BUILD_TYPE=Release -S . -B build{i}", *result)

for i, _ in enumerate(results):
    print(f"cmake --build build{i}")
