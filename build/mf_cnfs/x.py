import itertools

def count_diff_lines(file1, file2):
    with open(file1, 'r') as f1, open(file2, 'r') as f2:
        lines1 = f1.readlines()
        lines2 = f2.readlines()
    max_len = max(len(lines1), len(lines2))
    diff = 0
    for i in range(max_len):
        line1 = lines1[i].rstrip('\n') if i < len(lines1) else ''
        line2 = lines2[i].rstrip('\n') if i < len(lines2) else ''
        if line1 != line2:
            diff += 1
    return diff

# list your 10 file paths here
files = [f"output_{i}.cnf" for i in range(1,10)]

results = {}
for f1, f2 in itertools.combinations(files, 2):
    diff = count_diff_lines(f1, f2)
    results[(f1, f2)] = diff

for pair, diff in results.items():
    print(f"{pair[0]} vs {pair[1]}: {diff} different lines")
