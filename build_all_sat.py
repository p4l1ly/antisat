flags0 = [
    # ([], None, [["sat"], ["afa"]]),
    ([], None, [["sat"]]),
    ([], None, [["trie"], ["clause"]]),
    (["sat", "trie"], ("MODE", "SAT_TRIE_HEAP"), [[]]),
    (["sat", "trie"], ("MODE", "SAT_TRIE_BUBBLE"), [[]]),
    (["sat", "trie"], ("MODE", "SAT_TRIE_WATCH"), [["watch"]]),
    (["sat", "clause"], ("MODE", "SAT_CLAUSE_HEAP"), [[]]),
    (["sat", "clause"], ("MODE", "SAT_CLAUSE_BUBBLE"), [[]]),
    (["sat", "clause"], ("MODE", "SAT_CLAUSE_WATCH"), [["watch"]]),
    ([], ("NEW_ANALYZE", "OFF"), [[]]),
    # ([], ("NEW_ANALYZE", "ON"), [[]]),
    ([], ("STRENGTHENCC", "OFF"), [[]]),
    ([], ("STRENGTHENCC", "ON"), [[]]),
    # (["sat", "trie"], ("SOLIDIFY", "OFF"), [[]]),
    (["sat", "trie"], ("SOLIDIFY", "ON"), [[]]),
    (["trie"], ("ALL_SOLO", "OFF"), [[]]),
    (["trie"], ("ALL_SOLO", "ON"), [[]]),
    (["watch"], ("WATCH_LEARNT_WATCH", "OFF"), [[]]),
    # (["watch"], ("WATCH_LEARNT_WATCH", "ON"), [[]]),
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
        results.add(settings)

recur(flags0, frozenset(), frozenset(), frozenset())

for i, result in enumerate(results):
    print(f"cmake -DCMAKE_BUILD_TYPE=Release -S . -B buildsat{i}", *result)

for i, _ in enumerate(results):
    print(f"cmake --build buildsat{i}")
