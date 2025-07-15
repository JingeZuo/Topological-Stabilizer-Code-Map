import numpy as np
from z3 import *
from functools import reduce

# 参数设置
k = 16
n = 16
X = [[Bool(f'x{i}_{j}') for j in range(n)] for i in range(k)]
target_add = []
charstab=[
    [1, 3],
    [1, 2],
    [9, 10],
    [10, 12],
    [5, 6],
    [5, 7],
    [14, 16],
    [13, 14],
[1, 2, 3, 4],
    [5, 6, 7, 8],
    [9, 10, 11, 12],
    [13, 14, 15, 16]
]
s = Solver()
for i in range(len(charstab)):
    q=np.zeros((1,n))
    for j in range(len(charstab[i])):
        q[0][charstab[i][j]-1] =1
    target_add.append(q[0])

# 添加加法约束：x1 + x2 == target_add （即异或）
for i in range(n):
    s.add(Xor(X[0][i], X[2][i]) == BoolVal(target_add[0][i]))
for i in range(n):
    s.add(Xor(X[4][i], X[5][i]) == BoolVal(target_add[1][i]))
for i in range(n):
    s.add(Xor(X[8][i], X[9][i]) == BoolVal(target_add[2][i]))
for i in range(n):
    s.add(Xor(X[12][i], X[14][i]) == BoolVal(target_add[3][i]))
for i in range(n):
    s.add(Xor(X[0][i], X[1][i]) == BoolVal(target_add[4][i]))
for i in range(n):
    s.add(Xor(X[4][i], X[6][i]) == BoolVal(target_add[5][i]))
for i in range(n):
    s.add(Xor(X[8][i], X[10][i]) == BoolVal(target_add[6][i]))
for i in range(n):
    s.add(Xor(X[12][i], X[13][i]) == BoolVal(target_add[7][i]))
for i in range(n):
    variables = [X[0][i], X[1][i], X[2][i], X[3][i]]
    xor_expr = reduce(Xor, variables)
    s.add(xor_expr == BoolVal(target_add[8][i]))
for i in range(n):
    variables = [X[4][i], X[5][i], X[6][i], X[7][i]]
    xor_expr = reduce(Xor, variables)
    s.add(xor_expr == BoolVal(target_add[9][i]))
for i in range(n):
    variables = [X[8][i], X[9][i], X[10][i], X[11][i]]
    xor_expr = reduce(Xor, variables)
    s.add(xor_expr == BoolVal(target_add[10][i]))
for i in range(n):
    variables = [X[12][i], X[13][i], X[14][i], X[15][i]]
    xor_expr = reduce(Xor, variables)
    s.add(xor_expr == BoolVal(target_add[11][i]))
# 可选：添加点积约束 x1·x2 ≡ 1 mod 2
for i in range(k):
    for j in range(k):
        if i+8 == j:
            dot_product = reduce(lambda a, b: Xor(a, b), [And(X[i][i], X[j][i]) for i in range(n)], False)
            s.add(dot_product)
        else:
            dot_product = reduce(lambda a, b: Xor(a, b), [And(X[i][i], X[j][i]) for i in range(n)], True)
            s.add(dot_product)
for i in range(k):
    for i in range(k):
        s.add(Not(And([Not(X[i][j]) for j in range(n)])))
for i in range(k):
    for j in range(i + 1, k):
        # 向量 X[i] 和 X[j] 不相等
        s.add(Not(And([X[i][p] == X[j][p] for p in range(n)])))
# 求解
if s.check() == sat:
    m = s.model()
    def get_vector(model, vec):
        return [1 if is_true(model.eval(v)) else 0 for v in vec]
    sol = []
    for i in range(k):
        sol.append(get_vector(m, X[i]))
    for i in range(k):
        print(f'x{i+1}=', sol[i])
print(s.check())  # 看看是不是 unsat
#%%

k = 4
n = 8
X = [[Bool(f'x{i}_{j}') for j in range(n)] for i in range(k)]
target_add = [1,1,1,0,1,0,1,0]
s = Solver()
for i in range(n):
    variables = [X[0][i], X[1][i], X[2][i], X[3][i]]
    xor_expr = reduce(Xor, variables)
    s.add(xor_expr == BoolVal(target_add[i]))
dot_product = reduce(lambda a, b: Xor(a, b), [And(X[0][i], X[1][i]) for i in range(n)], True)
s.add(dot_product)
for i in range(k):
    for i in range(k):
        s.add(Not(And([Not(X[i][j]) for j in range(n)])))
for i in range(k):
    for j in range(i + 1, k):
        # 向量 X[i] 和 X[j] 不相等
        s.add(Not(And([X[i][p] == X[j][p] for p in range(n)])))
if s.check() == sat:
    m = s.model()
    def get_vector(model, vec):
        return [1 if is_true(model.eval(v)) else 0 for v in vec]
    sol = []
    for i in range(k):
        sol.append(get_vector(m, X[i]))
    for i in range(k):
        print(f'x{i+1}=', sol[i])
print(s.check())  # 看看是不是 unsat


