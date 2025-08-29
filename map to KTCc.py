from itertools import combinations
import numpy as np
from z3 import *
from functools import reduce
def commute(a, b, init_val):
    indices = ([(i, (i+8)%16 ) for i in range(16)])
    terms = []
    for i, j in indices:
        if j < len(b):  # 确保不会越界
            terms.append(And(a[i], b[j]))
    return reduce(Xor, terms, init_val)
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
k = 16
n = 16
X = [[Bool(f'x{i}_{j}') for j in range(n)] for i in range(k)]
target_add = []
char = [
    [5],
    [1],
    [6],
    [2],
    [9],
    [13],
    [10],
    [14],
[4],
    [8],
    [11,12],
    [15,16]
]
stab = [[3],
        [12],
        [7],
        [16]]
CCchar = [[1, 3],
          [1, 2],
          [5, 6],
          [5, 7],
          [9, 11],
          [9, 10],
          [13, 14],
          [13, 15],
          [4],
          [8],
          [12],
          [16]]
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
        if len(CCchar[i]) != 1:
            constraint = (Xor(X[CCchar[i][0] - 1][j], X[CCchar[i][1] - 1][j]) == BoolVal(target_add[i][j]))
            s.assert_and_track(constraint, f'c{i}_{j}')
        if len(CCchar[i]) == 1:
            constraint = (X[CCchar[i][0] - 1][j] == BoolVal(target_add[i][j]))
            s.assert_and_track(constraint, f'c{i}_{j}')
for i in range(len(stab)):
    for j in range(n):
        variables = [X[CCstab[i][0] - 1][j], X[CCstab[i][1] - 1][j], X[CCstab[i][2] - 1][j], X[CCstab[i][3] - 1][j]]
        xor_expr = reduce(Xor, variables)
        constraint = (xor_expr == BoolVal(target_add[len(char) + i][j]))
        s.assert_and_track(constraint, f'c{len(char) + i}_{j}')

for i in range(k):
    for j in range(k):
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

#%%
def vec_add_mod2_with_indices(*vecs):
    """
    对多个二进制向量进行模 2 加法（GF(2)），并返回结果向量和非零元素的索引（从 1 开始）。

    参数:
        *vecs: 任意数量的等长二进制向量（列表或元组）

    返回:
        tuple: (result_vector: list, indices: list)
               result_vector 是模 2 加法后的向量
               indices 是值为 1 的位置索引（从 1 开始）
    """
    if not vecs:
        return [], []

    # 检查向量长度是否一致
    length = len(vecs[0])
    if not all(len(v) == length for v in vecs):
        raise ValueError("All vectors must have the same length.")

    # 模 2 加法：每一列求和后 mod 2
    result_vector = [sum(col) % 2 for col in zip(*vecs)]

    # 获取值为 1 的索引（从 1 开始编号）
    indices = [i + 1 for i, val in enumerate(result_vector) if val == 1]

    return result_vector, indices
print(vec_add_mod2_with_indices(sol[0],sol[1],sol[2],sol[3],sol[4],sol[5],sol[6],sol[7]))
#%%
sol=[[1,3,4,5],
     [3,4,5],
[1,3,4],
     [4],
     [2,6,7,8],
     [2,7,8],
     [6,7,8],
[8],
     [9,11,13],
     [9,11],
     [11,13],
[11,12],
     [10,14,15],
     [14,15],
[10,15],
[15,16]
     ]
soltion=[]
for i in range(len(sol)):
    a=np.zeros((1,16))[0]
    for j in range(len(sol[i])):
        a[sol[i][j]-1]=1
    soltion.append(a.tolist())
print(soltion[12])
#%%
for i in range(len(soltion)):
    for j in range(len(soltion)):
        if j == (i + 8) % 16:
            a = [BoolVal(bool(x)) for x in soltion[i]]
            b = [BoolVal(bool(x)) for x in soltion[j]]
            result = commute(a, b, BoolVal(False))
            if simplify(result)==False:
                print(simplify(result), i, j)  # True
        else:
            a = [BoolVal(bool(x)) for x in soltion[i]]
            b = [BoolVal(bool(x)) for x in soltion[j]]
            result = commute(a, b, BoolVal(True))
            if simplify(result) == False:
                print(simplify(result), i, j)  # True

#%%
for i in range(len(stab)):
    for j in range(n):
        a = [BoolVal(bool(x)) for x in soltion[CCstab[i][0] - 1]]
        b = [BoolVal(bool(x)) for x in soltion[CCstab[i][1] - 1]]
        c = [BoolVal(bool(x)) for x in soltion[CCstab[i][2] - 1]]
        d = [BoolVal(bool(x)) for x in soltion[CCstab[i][3] - 1]]
        variables = [a[j], b[j], c[j], d[j]]
        xor_expr = reduce(Xor, variables)
        constraint = (xor_expr == BoolVal(target_add[len(char) + i][j]))
        if simplify(constraint)==False:
            print(simplify(constraint))
#%%
for i in range(len(char)):
    for j in range(n):
        a = [BoolVal(bool(x)) for x in soltion[CCchar[i][0] - 1]]
        if len(CCchar[i]) != 1:
            b = [BoolVal(bool(x)) for x in soltion[CCchar[i][1] - 1]]
            constraint = (Xor(a[j], b[j]) == BoolVal(target_add[i][j]))
            if simplify(constraint)==False:
                print(simplify(constraint),i,j)
        if len(CCchar[i]) == 1:
            constraint = (a[j] == BoolVal(target_add[i][j]))
            if simplify(constraint)==False:
                print(simplify(constraint),i,j)
#%%
print(sol[0],ind[0],sol[2],ind[2])
