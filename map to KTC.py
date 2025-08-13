from itertools import combinations
import numpy as np
from z3 import *
from functools import reduce
def commute(a, b, init_val):
    indices = ([(i, (i+1)) for i in [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31]]+[((i+1), i) for i in [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31]])
    terms = []
    for i, j in indices:
        if j < len(b)+1:  # 确保不会越界
            terms.append(And(a[i-1], b[j-1]))
    return reduce(Xor, terms, init_val)
def is_2j_relation(a, b):
    """
    判断两个数是否满足 2j-1 和 2j 的关系
    """
    # 确保 a 是较小的数
    if a > b:
        a, b = b, a

    # 检查是否满足 b = a + 1 且 a 是奇数
    return b == a + 1 and a % 2 == 1
# 参数设置
k = 32
n = 32
X = [[Bool(f'x{i}_{j}') for j in range(n)] for i in range(k)]
target_add = []
char = [
    [4],
    [3],
    [2],
    [1],
    [11],
    [12],
    [9],
    [10],
    [16],
    [15],
    [14],
    [13],
    [7],
    [8],
    [5],
    [6],
    [19],
    [18,20],
    [23],
    [22,24],
[27],
[26,28],
[31],
[30,32]]
stab = [[17],
        [20],
        [21],
        [24],
        [25],
        [28],
        [29],
        [32]]
CCchar = [[2,6],
          [1,3],
          [10,12],
          [9, 13],
          [1,5],
          [2,4],
          [9,11],
          [10, 14],
          [18,22],
          [17,19],
          [26,28],
          [25,29],
          [17,21],
          [18,20],
          [25,27],
          [26,30],
          [7],
          [8],
          [15],
          [16],
          [23],
          [24],
          [31],
          [32]]
CCstab = [[1,3,5,7],
          [2,4,6,8],
          [9,11,13,15],
          [10,12,14,16],
          [17,19,21,23],
          [18,20,22,24],
          [25,27,29,31],
          [26,28,30,32]]
charstab = char + stab
for i in range(len(charstab)):
    q = np.zeros((1, n), dtype=int)
    for j in range(len(charstab[i])):
        q[0][charstab[i][j] - 1] = 1
    target_add.append(q[0])
#%%
s = Solver()
for i in range(len(char)):
    for j in range(n):
        if len(CCchar)==2:
            constraint = (Xor(X[CCchar[i][0] - 1][j], X[CCchar[i][1] - 1][j]) == BoolVal(target_add[i][j]))
            s.assert_and_track(constraint, f'c{i}_{j}')
        if len(CCchar)==1:
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
        if is_2j_relation(i+1,j+1)==True:
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
sol=[[3,11,17,19],
     [4,12,18],
     [11,17,19],
     [4,18],
     [3,17,19],
     [12,18],
     [19],
     [18,20],

     [1,9,21,23],
     [2,10,22],
     [1,21,23],
     [10,22],
     [9,21,23],
     [2,22],
     [23],
     [22,24],

     [7,15,25,27],
     [8,16,26],
     [7,25,27],
     [16,26],
     [15,25,27],
     [8,26],
     [27],
     [26,28],

     [5,13,29,31],
     [6,14,30],
     [13,29,31],
     [6,30],
     [5,29,31],
     [14,30],
     [31],
     [30,32]]
soltion=[]
for i in range(len(sol)):
    a=np.zeros((1,n))[0]
    for j in range(len(sol[i])):
        a[sol[i][j]-1]=1
    soltion.append(a.tolist())
print(len(soltion))
#%%
for i in range(len(soltion)):
    for j in range(len(soltion)):
        if is_2j_relation((i+1),(j+1)):
            a = [BoolVal(bool(x)) for x in soltion[i]]
            b = [BoolVal(bool(x)) for x in soltion[j]]
            result = commute(a, b, BoolVal(False))
            if simplify(result)==False:
                print(simplify(result),i,j)  # True
        else:
            a = [BoolVal(bool(x)) for x in soltion[i]]
            b = [BoolVal(bool(x)) for x in soltion[j]]
            result = commute(a, b, BoolVal(True))
            if simplify(result) == False:

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
        if len(CCchar[i]) ==2:
            b = [BoolVal(bool(x)) for x in soltion[CCchar[i][1] - 1]]
            constraint = (Xor(a[j], b[j]) == BoolVal(target_add[i][j]))
            if simplify(constraint)==False:
                print(simplify(constraint),i,j)
        if len(CCchar[i]) == 1:
            constraint = (a[j] == BoolVal(target_add[i][j]))
            if simplify(constraint)==False:
                print(simplify(constraint),i,j)
#%%
for i in range(k):
    a=[BoolVal(bool(x)) for x in soltion[i]]
    s=Not(And([Not(a[j]) for j in range(n)]))
    if simplify(s)==False:
        print(simplify(s))
#%%
for i in range(k):
    for j in range(i + 1, k):
        a = [BoolVal(bool(x)) for x in soltion[i]]
        b=[BoolVal(bool(x)) for x in soltion[j]]
        s = Not(And([a[p] == b[p] for p in range(n)]))
        if simplify(s)==False:
            print(simplify(s))
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
print(vec_add_mod2_with_indices(soltion[5], soltion[7],soltion[17],soltion[21],soltion[25],soltion[11],soltion[15],soltion[27]))
