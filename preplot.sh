cat bench.log | cut -d' ' -f'3,9,15,21' | tr ' ' '\t' > bench.csv
