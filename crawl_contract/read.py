import os
import json

# 文件位置
# ./dataset
# ./bugs/sailfish_tod
path = "./bugs/sailfish_tod"

contractl = os.listdir(path)
contractl.sort(key=lambda x:int(x))

for contracts in contractl:
    file_path = path + "/" + contracts
    with open(file_path, 'r') as f:
        contractj = json.loads(f.read())
        # 每个文件有100个合约
        for contract in contractj:
            # 每个合约包含ContractName Address SourceCode CompilerVersion EVMVersion ContractByteCode属性
            print(contract['ContractName'])

# file_path = path + "/" + str(27)
# with open(file_path, 'r') as f:
#     contractj = json.loads(f.read())
#     for contract in contractj:
#         # 每个合约包含ContractName Address SourceCode CompilerVersion EVMVersion ContractByteCode属性
#         print(contract['ContractName'])
