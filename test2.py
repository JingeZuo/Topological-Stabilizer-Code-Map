from itertools import combinations

import numpy as np
from z3 import *
from functools import reduce
def commute(a, b, init_val):
    indices = ([(i, (i+9) % 18) for i in (5,7,14,16)]+[(i, (i+7) % 14) for i in (2,4,9,11)]+
               [(i,i+1) for i in (17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55)]+[(i+1,i) for i in (17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55)])
    terms = []
    for i, j in indices:
        if j < len(b):  # 确保不会越界
            terms.append(And(a[i-1], b[j-1]))
    return reduce(Xor, terms, init_val)
br=[
    [6,10],
    [0,14],
    [0,12],
    [7,9],
    [5,9],
    [6,8],
[0,15],
[2,15]
]
br1=[
    [6,10],
    [0,14],
    [0,12],
    [7,9],
    [6,15],
    [5,15],
    [4,15],
    [5,9],
    [6,8],
[0,15],
[7,15],
[2,15]
]
def op(br):
    # 参数设置
    k = 16
    n = 56
    X = [[Bool(f'x{i}_{j}') for j in range(n)] for i in range(k)]
    target_add = []
    char = [
        [1, 3, 13, 14, 15, 16],
        [5, 7],
        [1, 2, 13, 14],
        [5, 6, 9, 10],
        [1, 3, 14, 16],
        [5, 7, 9, 11],
        [1, 2],
        [5, 6]
    ]
    stab = [[1, 2, 3, 4, 13, 14, 15, 16, 18,26,34,42,50],
            [5, 6, 7, 8, 9, 10, 11, 12, 20,28,36,44,52],
            [1, 2, 3, 4, 22,30,38,46,54],
            [5, 6, 7, 8, 24,32,40,48,56]]
    CCchar = [[1, 3],
              [9, 11],
              [1, 2],
              [9, 10],
              [5, 7],
              [13, 15],
              [5, 6],
              [13, 14]]
    CCstab = [[1, 2, 3, 4],
              [9, 10, 11, 12],
              [5, 6, 7, 8],
              [13, 14, 15, 16]]
    charstab = char + stab
    s = Solver()
    for i in range(len(charstab)):
        q = np.zeros((1, n), dtype=int)
        for j in range(len(charstab[i])):
            q[0][charstab[i][j] - 1] = 1
        target_add.append(q[0])
    for i in range(len(char)):
        for j in range(n):
            constraint = (Xor(X[CCchar[i][0] - 1][j], X[CCchar[i][1] - 1][j]) == BoolVal(target_add[i][j]))
            s.assert_and_track(constraint, f'c{i}_{j}')
    for i in range(len(stab)):
        for j in range(n):
            variables = [X[CCstab[i][0] - 1][j], X[CCstab[i][1] - 1][j], X[CCstab[i][2] - 1][j], X[CCstab[i][3] - 1][j]]
            xor_expr = reduce(Xor, variables)
            constraint = (xor_expr == BoolVal(target_add[len(char) + i][j]))
            s.assert_and_track(constraint, f'c{len(char) + i}_{j}')

    for i in range(k):
        for j in range(k):
            skip = False
            for l in range(len(br)):
                if (i == br[l][0] and j == br[l][1]) or (i == br[l][1] and j == br[l][0]):
                    skip = True
                    break
            if skip:
                continue
            if j == (i + 8) % 16:
                s.assert_and_track(commute(X[i], X[j], init_val=False), f'c{len(charstab) + i}_{j}')
            else:
                s.assert_and_track(commute(X[i], X[j], init_val=True), f'c{len(charstab) + i}_{j}')

    for i in range(k):
        s.assert_and_track(Not(And([Not(X[i][j]) for j in range(n)])), f'c{len(charstab) + k + i}_{j}')
    for i in range(k):
        for j in range(i + 1, k):
            # 向量 X[i] 和 X[j] 不相等
            s.assert_and_track(Not(And([X[i][p] == X[j][p] for p in range(n)])), f'c{len(charstab) + 2 * k + i}_{j}')

    # 求解
    if s.check() == sat:
        m = s.model()

        def get_vector(model, vec):
            return [1 if is_true(model.eval(v)) else 0 for v in vec]

        sol = []
        for i in range(k):
            sol.append(get_vector(m, X[i]))
        for i in range(k):
            ind = []
            for j in range(len(sol[i])):
                if sol[i][j] != 0:
                    ind.append(j + 1)
            print(f'x{i + 1}=', sol[i], ind)
    else:
        print("Solver is unsatisfiable. Analyzing which commute constraints are in conflict...")
        s.set(unsat_core=True)
        core = s.unsat_core()
        num_charstab = len(charstab)
        conflict_commute = []
        for c in core:
            name = str(c)
            if name.startswith('c') and '_' in name:
                try:
                    parts = name[1:].split('_')
                    idx1 = int(parts[0])
                    if idx1 >= num_charstab:
                        i = idx1 - num_charstab
                        if i < k:
                            j = int(parts[1])
                            if j < k:
                                conflict_commute.append((i, j))
                except:
                    continue

        if conflict_commute:
            print("The following commute constraints are in conflict with other constraints:")
            for i, j in conflict_commute:
                print(f"  commute(X[{i}], X[{j}])")
        else:
            print("No commute constraint is in the unsat core. Conflict comes from non-commute constraints.")

    print(len(br))
op(br)
#%%
def remove_nth_to_new_list(lst, n):
    """
    从列表中删除第 n 个元素（n 从 1 开始），返回一个新列表，原列表不变。

    参数:
    lst: 原始列表
    n: 要删除的元素位置（从 1 开始计数）

    返回:
    新列表（不含第 n 个元素）
    """
    if n < 1 or n > len(lst):
        raise IndexError(f"n 超出范围！列表长度为 {len(lst)}，n 应在 1 到 {len(lst)} 之间。")

    # 使用切片组合：前 n-1 个 + 从第 n 个之后的
    return lst[:n - 1] + lst[n:]
for i in range(len(br)):
    op(remove_nth_to_new_list(br,i+1))
    print(i+1)
#%%
result = [[x+1, y+1] for x, y in br]
# 逐行输出
for item in result:
    print(item)
print(len(result))
