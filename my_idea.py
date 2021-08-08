'''
Title:  Flexible revocation in ciphertext-policy attribute-based encryption with verifiable ciphertext delegation
Author: Deng
Date:   2019/6/2
'''

from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, pair, GT
from charm.toolbox.secretutil import SecretUtil
from random import choice

debug = False

class StateInformation:
    def __init__(self, tree_depth, groupObj):
        self.group = groupObj
        self.tree_depth = tree_depth
        self.user_set = set()
        self.node_set = set()
        self.node_unassignedleafnode = set()
        for i in range(2 ** tree_depth):
            self.node_unassignedleafnode.add(i)  # 初始化所有叶子节点，个数为2 ^ tree_depth
        self.node_value = {}
        self.node_set.add('root')
        for j in range(2 ** tree_depth):
            temp = bin(j)  # 将十进制转化为二进制（如： bin(1) = 0b1 / bin(3) = 0b11 ）
            temp = temp[:2] + (tree_depth - len(temp) + 2) * '0' + temp[2:]  # temp[:2] temp字符串前两个字符 temp[2:] temp 字符串除去前两个字符 统一格式
            for depth in range(1, self.tree_depth + 1):
                self.node_set.add(temp[0:depth + 2])
        self.user_assignment = {}

    def KUNode(self, RL):
        X = set()
        Y = set()
        for GID in RL:
            X = X.union(self.user_assignment[GID]['path'])
        if len(RL) == 0:
            Y.add('root')
            return Y
        else:
            if '0b1' not in X:
                Y.add('0b1')  # deal with the root node
            for theta in X:
                if theta == 'root':
                    continue
                else:
                    if len(theta) < self.tree_depth + 2:  # exclude the leaf node
                        if (theta + '0') not in X:
                            Y.add(theta + '0')
                        if (theta + '1') not in X:
                            Y.add(theta + '1')
            return Y

    def Update(self, GID):
        if GID in self.user_set:
            print('Registered GID')
            return
        self.user_assignment[GID] = {}
        temp = choice(list(self.node_unassignedleafnode))
        self.node_unassignedleafnode.remove(temp)
        temp = bin(temp)
        temp = temp[:2] + (self.tree_depth - len(temp) + 2) * '0' + temp[2:]
        self.user_assignment[GID]['leafnode'] = temp
        self.user_assignment[GID]['value'] = self.group.random(ZR)
        self.user_assignment[GID]['path'] = set()
        self.user_assignment[GID]['path'].add('root')
        for depth in range(1, self.tree_depth + 1):
            self.user_assignment[GID]['path'].add(temp[0:depth + 2])
        self.user_set.add(GID)
        return self

class TimeStructure:
    def __init__(self, bounded_time):
        time_t = bin(bounded_time).replace('0b','')
        self.size = len(time_t)

    def TEncode(self, t):
        string_t = bin(t).replace('0b','')
        while (len(string_t) < self.size):
            string_t = '0'+string_t
        #print(string_t)
        return string_t

    def CTEncode(self, time):
        chk = False
        string_time = self.TEncode(time)
        for i in range(self.size):
            if string_time[i] == '1' and chk == False:
                continue
            else:
                chk = True
                string_time = string_time[:i] + '0' + string_time[i+1:]
        #print(string_time)
        return string_time

class FRABE:

    def __init__(self, groupObj):
        #global group
        self.group = groupObj
        self.util = SecretUtil(groupObj, verbose=False)

    def setup(self, user_depth, attribute_set, bound_time):
        if debug: print("Setup alg...")
        st = StateInformation(user_depth, self.group)
        self.ti = TimeStructure(bound_time)
        #global ti
       # ti.CTEncode(2000)
        g = self.group.random(G1)
        h = self.group.random(G1)
        w = self.group.random(G1)
        alpha = self.group.random(ZR)
        e_gh_alpha = pair(h, g ** alpha)
        r_i = {}
        T_i = {}
        U = self.group.random(G1)
        U_j = {}
        for attr in attribute_set:
            r_i[attr] = self.group.random(ZR)
            T_i[attr] = g ** (-r_i[attr])
        for j in range(self.ti.size):
            U_j[j] = self.group.random(G1)
        pk = {'g': g, 'h': h, 'w': w, 'e_gh_alpha': e_gh_alpha, 'T_i': T_i, 'attr_set': attribute_set, 'U': U, 'U_j': U_j}
        mk = {'alpha': alpha, 'r_i': r_i, 'st': st}
        return (pk, mk)

    def OskGEN(self, pk, mk, S, ID):
        if debug: print("OskGEN alg...")
        mk['st'].Update(ID)
        msk = {}
        for attr in S:
            msk[attr] = {}
            for node in mk['st'].user_assignment[ID]['path']:
                if mk['st'].node_value.get(node) == None:
                    mk['st'].node_value[node] = self.group.random(ZR)
                msk[attr][node] = (pk['w'] ** (mk['st'].node_value[node] + mk['r_i'][attr])) * (pk['h'] ** mk['st'].user_assignment[ID]['value'])
        g_u = pk['g'] ** mk['st'].user_assignment[ID]['value']
        return {'g_u': g_u, 'msk': msk, 'ID': ID}

    def UpmGEN(self, pk, mk, RLs, rl, time):
        if debug: print("UpmGEN alg...")
        string_t = self.ti.TEncode(time)
        ans = 1
        for i in range(self.ti.size):
            if (string_t[i] == '0'):
                ans *= pk['U_j'][i]
        TUM_t = pk['U'] * ans
        UUM_t = {}
        AUM_t = {}
        for user in mk['st'].user_set:
            UUM_t[user] = {}
            if user in rl:
                UUM_t[user] = None
            else:
                x = self.group.random(ZR)
                UUM_t[user][0] = (pk['h'] ** (mk['alpha']-mk['st'].user_assignment[user]['value'])) * (TUM_t ** x)
                UUM_t[user][1] = pk['g'] ** x
        for attr in pk['attr_set']:
            y = mk['st'].KUNode(RLs[attr])
            AUM_t[attr] = {}
            for node in y:
                if mk['st'].node_value.get(node) == None:
                    mk['st'].node_value[node] = self.group.random(ZR)
                AUM_t[attr][node] = (pk['w'] ** -(mk['st'].node_value[node] + mk['r_i'][attr])) * (TUM_t ** mk['r_i'][attr])
        return (TUM_t, UUM_t, AUM_t)

    def OriEnc(self, pk, m, policy_str, time):
        if debug: print("OriEnc alg...")
        policy = self.util.createPolicy(policy_str)
        s = self.group.random(ZR)
        shares = self.util.calculateSharesDict(s, policy)
        ######################################################
        c_1 = m * (pk['e_gh_alpha'] ** s)
        c_2 = pk['g'] ** s
        U = pk['U'] ** s
        c_i = {}
        U_i = {}
        for i in shares.keys():
            c_i[i] = pk['h'] ** (shares[i] - s)
        str_plus = self.ti.CTEncode(time)
        for i in range(self.ti.size):
            if (str_plus[i] == '0'):
                U_i[i] = pk['U_j'][i] ** s
            else:
                U_i[i] = None
        return {'c_1': c_1, 'c_2': c_2, 'c_i': c_i, 'policy': policy_str, 'U': U, 'U_i': U_i, 't': time}

    def CirReEnc(self, pk, ct, time):
        if debug: print("CirReEnc alg...")
        if (time < ct['t']):
            return False
        yimixilo = self.group.random(ZR)
        policy = self.util.createPolicy(ct['policy'])
        shares = self.util.calculateSharesDict(yimixilo, policy)

        c_1 = ct['c_1'] * (pk['e_gh_alpha'] ** yimixilo)
        c_2 = ct['c_2'] * (pk['g'] ** yimixilo)
        str_time = self.ti.TEncode(time)
        Tim1 = ct['U']
        Tim2 = pk['U']
        for i in range(self.ti.size):
            if (str_time[i] == '0'):
                Tim1 *= ct['U_i'][i]
                Tim2 *= pk['U_j'][i]
        c_3 = Tim1 * (Tim2 ** yimixilo)
        c_i = {}
        for i in shares.keys():
            c_i[i] = ct['c_i'][i] * (pk['h'] ** (shares[i] - yimixilo))
        return {'c_1': c_1, 'c_2': c_2, 'c_3': c_3, 'c_i': c_i, 'policy': ct['policy']}

    def DskGEN(self, Osk, AUM_t):
        if debug: print("DskGEN alg...")
        msk = {}
        for attr in Osk['msk']:
            for node in Osk['msk'][attr]:
                if node in AUM_t[attr]:
                    msk[attr] = Osk['msk'][attr][node] * AUM_t[attr][node]
        return {'g_u': Osk['g_u'], 'msk': msk, 'ID': Osk['ID']}

    def CirDec(self, pk, Dsk, ct_t, UUM_t):
        if debug: print("CirDec alg...")
        if Dsk['ID'] not in UUM_t:  # 若用户被撤销，直接return False
            return False
        policy = self.util.createPolicy(ct_t['policy'])
        S = set()
        for attr in Dsk['msk']:
            S.add(attr)
        pruned_list = self.util.prune(policy, S)
        if pruned_list == False:  # 如果不满足，直接返回False
            return False
        omiga = self.util.getCoefficients(policy)  # 取LSSS中的欧米伽 ??
        A = 1
        for i in pruned_list:
            j = i.getAttributeAndIndex()
            k = i.getAttribute()
            A *= (pair(Dsk['msk'][k], ct_t['c_2']) * pair(ct_t['c_3'], pk['T_i'][j]) * pair(ct_t['c_i'][j], Dsk['g_u'])) ** omiga[j]
        #a = pair(ct_t['c_2'], pk['h']) ** mk['st'].user_assignment[Dsk['ID']]['value']
        B = pair(UUM_t[Dsk['ID']][0], ct_t['c_2']) / pair(ct_t['c_3'], UUM_t[Dsk['ID']][1])
        #b = pair(ct_t['c_2'], pk['h']) ** (mk['alpha']-mk['st'].user_assignment[Dsk['ID']]['value'])
        return ct_t['c_1'] / (A * B)

    def Verified(self, pk, ct_t, TUM_t):
        a1 = pair(ct_t['c_3'], pk['g'])
        a2 = pair(TUM_t, ct_t['c_2'])
        assert a1 == a2, "CSP updated wrong !"
        b1 = pair(ct_t['c_2'], pk['h'])
        policy = self.util.createPolicy(ct_t['policy'])
        S = {'ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX'}
        pruned_list = self.util.prune(policy, S)
        omiga = self.util.getCoefficients(policy)
        b2 = 1
        for i in pruned_list:
            j = i.getAttributeAndIndex()
            b2 *= (pair(pk['h'], ct_t['c_2']) * pair(ct_t['c_i'][j], pk['g'])) ** omiga[j]
        assert b1 == b2, "CSP updated wrong !"

def main():
    groupObj = PairingGroup('SS512')
    myabe = FRABE(groupObj)
    attribute = {'ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX'}
    user_depth = 4
    (pk, mk) = myabe.setup(user_depth, attribute, 2047)
    user = {}
    ID = 'DXX'
    S = {'ONE', 'TWO', 'THREE'}
    user[ID] = {'ID': ID, 'Attribute': S, 'Osk': None, 'Dsk': None}
    user[ID]['Osk'] = myabe.OskGEN(pk, mk, user[ID]['Attribute'], user[ID]['ID'])
  #  for i in range(1, 4):
   #    user[ID]['Osk'] = myabe.OskGEN(pk, mk, user[ID]['Attribute'], user[ID]['ID'])
   # print(user['DXX']['Osk'])
    RLs = {'ONE':{}, 'TWO':{'DXX'}, 'THREE':{}, 'FOUR':{}, 'FIVE':{}, 'SIX':{}}
    rl = {}
    (T, U, A) = myabe.UpmGEN(pk, mk, RLs, rl, 1000)
  #  return
    m = groupObj.random(GT)
    policy_str = '(ONE or TWO) and THREE'
    ct = myabe.OriEnc(pk, m, policy_str, 800)
    #print(ct)
    ct_t = myabe.CirReEnc(pk, ct, 1000)
    #print(ct_t)
    user[ID]['Dsk'] = myabe.DskGEN(user[ID]['Osk'], A)
   # print(user)
    dec_mes = myabe.CirDec(pk, user[ID]['Dsk'], ct_t, U)

    assert dec_mes != False, "not satisfies policy"
    assert dec_mes == m, "Failed Decryption!!"
    print("SUCCESS DECRYPT!!!")
    myabe.Verified(pk, ct_t, T)
    print("CSP updated right !!")


if __name__ == "__main__":
    debug = True
    main()
