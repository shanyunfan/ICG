# encoding: utf-8
import copy
import math
import time
import random
import string
import matplotlib
import networkx as nx
import matplotlib.pyplot as plt



def load_data(path):
    """
    path: 文件路径
    """
    print('数据集加载中......')
    lists = []
    G = nx.Graph()  # 创建空的简单图

    with open(path) as file:
        val_list = file.readlines()  # 将文件转换为所有的行组成的列表
    for string in val_list:
        v1, v2 = string.split(' ', 1)
        v1 = int(v1)
        v2 = int(v2)
        if v1 != v2:
            lists.append((v1, v2))  # 只取每个string的前三项，得到的lists即为所要的列表
    G.add_edges_from(lists)  # 按照lists中的边保存图

    print('数据读取完毕')
    return G

def FGA(G):
    A = set()                          #A以集合的形式保存
    Det = {}
    Unsat = {}

    for i in G.nodes():
        det = int((G.degree(i) + 1) / 2)
        Det[i] = det
        Unsat[i] = len(set(G.neighbors(i)))

    for i in G.nodes():
        if Det[i] > 0:
            D = Det[i]
            nei_i = set(G.neighbors(i))
            for j in range(D):    #找unsat最大值所对应的
                max_v = []
                R = [item for item in nei_i if item not in A]
                maxv = R[0]
                max = Unsat[maxv]
                for z in R:
                    if max < Unsat[z]:
                        max = Unsat[z]
                        #maxv = z
                for x in R:   #记录最大值并随机选一个
                    if Unsat[x] == max:
                        max_v.append(x)
                maxv = random.choice(max_v)
                #maxv = max_v[0]

                A.add(maxv)
                #print (maxv)
                nei = set(G.neighbors(maxv))
                for x in nei:
                    if Det[x] > 0:
                        Det[x] = Det[x] - 1
                        if Det[x] == 0:
                            nei_x = set(G.neighbors(x))
                            for y in nei_x:
                                Unsat[y] = Unsat[y] - 1
            nei_i.clear()

    return A

def DCR(G,A,b, nei):
    #破坏过程
    Lc = []  #接收拆除的点
    Lp = list(A)

    random.shuffle(Lp)   #乱序，排除顺序的影响
    for i in range(int(b * len(A))):     #拆除A中b%的点,给了Lc
        v = Lp.pop()
        Lc.append(v)

    Lp_set = set(Lp)
    #计算h,uncoverd
    h = {}
    uncoverd = set()  #保存未被覆盖的点

    for i in G.nodes():  # 统计uncover并保存
        dom_i = len(nei[i] & Lp_set)
        h[i] = dom_i - int((G.degree(i) + 1) / 2)
        if h[i] < 0:
            uncoverd.add(i)

    #旋转木马
    for i in range(len(A) - int(b * len(A))):
        v1 = Lp.pop(0)
        Lc.append(v1)
        #更新h,uncoverd
        for i in nei[v1]:
            h[i] = h[i] - 1
            if h[i] == -1:   #说明i由覆盖变为未被覆盖状态
                uncoverd.add(i)

        #从Lc中选一个点，要求这个点的邻居节点中未被覆盖的点的个数最大。  邻居节点中未被覆盖的点的个数
        t = Lc[0]
        maxu = len(nei[t] & uncoverd)

        for i in Lc:
            unsat_i = len(nei[i] & uncoverd)
            if maxu < unsat_i:
                maxu = unsat_i
                t = i

        Lc.remove(t)
        Lp.append(t)

        # 更新h，uncoverd
        for i in nei[t]:
            h[i] = h[i] + 1
            if h[i] == 0:  #说明i点由未覆盖变为被覆盖状态
                uncoverd.remove(i)
    #更新
    Lp0 = set(Lp)

    #return Lp0
    #FA重构
    #A = set()  # A以集合的形式保存
    #Det = -h !!
    Unsat = {}   #计算每个点的unsati
    for i in G.nodes():
        Unsat[i] = len(nei[i] & uncoverd)

    for i in G.nodes():
        if h[i] < 0:
            D = -1 * h[i]
            #nei_i = set(G.neighbors(i))
            for j in range(int(D)):  # 找unsat最大值所对应的
                max_v = []
                R = [item for item in nei[i] if item not in Lp0]
                maxv = R[0]
                max = Unsat[maxv]
                for z in R:
                    if max < Unsat[z]:
                        max = Unsat[z]
                        # maxv = z
                for x in R:  # 记录最大值并随机选一个
                    if Unsat[x] == max:
                        max_v.append(x)
                maxv = random.choice(max_v)

                Lp0.add(maxv)
                # print (maxv)
                #nei = set(G.neighbors(maxv))
                for x in nei[maxv]:
                    if h[x] < 0:
                        h[x]  = h[x] + 1
                        if h[x]  == 0:  #说明节点x变成被覆盖状态
                            #nei_x = nei[x]
                            for y in nei[x]:
                                Unsat[y] = Unsat[y] - 1
            #nei_i.clear()

    return Lp0




def run(G,Gmax,b):
    nei = {}  # 用字典保存邻居

    for i in G.nodes():
        nei[i] = set(G.neighbors(i))

    start1 = time.time()


    A0 = FGA(G)  # 用FA构建初始解
    Abest = A0.copy()
    print ("Local", len(Abest))
    Abest_len = len(Abest)

    for i in range(Gmax):  # 迭代Gmax次
        A2 = DCR(G, Abest, b, nei)  # 破坏并进行旋转木马
        A_2 = A2.copy()
        if len(A_2) <= Abest_len:  # 接收准则：如果比最优解好就接收
            Abest_len = len(A_2)
            Abest = A_2.copy()
        print("代数", i)
        print ("best_solution", len(Abest))
        end1 = time.time()
        print("当前用时", end1-start1)

    return Abest

if __name__ == "__main__":

    my_data = load_data('dolphin.txt')


    start = time.time()

    A = run(my_data,500,0.1)

    print(A)
    print(len(A))
    end = time.time()
    print('Running time total: %s Seconds' % (end - start))

    #A0 = test(my_data,A)
    #print ("A0",A0)
    #print ("lenA0", len(A0))


