import os
import json

# 文件位置
# ./dataset
# ./bugs/sailfish_tod
# path = "./bugs/sailfish_dao"
path = "./datasets"

contractl = os.listdir(path)
contractl.sort()

base = path + "/contracts"
os.mkdir(base)
for contracts in contractl:
    file_path = path + "/" + contracts
    with open(file_path, 'r') as f:
        contractj = json.loads(f.read())
        # 每个文件有100个合约
        for contract in contractj:
            # 每个合约包含ContractName Address SourceCode CompilerVersion EVMVersion ContractByteCode属性
            cv_content = contract['CompilerVersion'][1:].partition("+")[0].partition("-")[0]
            dirpath = base + "/" + str(contract['Address'])
            os.mkdir(dirpath)
            sfile_name = dirpath + "/" + str(contract['Address']) + '.sol'
            bfile_name = dirpath + "/" + str(contract['Address']) + '.byte'
            afile_name = dirpath + "/" + str(contract['Address']) + '.address'
            cv_name = dirpath + "/CompilerVersion"
            with open(cv_name, 'w') as fcv:
                fcv.write(cv_content)
                fcv.close()
            with open(sfile_name, 'w') as fn:
                fn.write(contract['SourceCode'])
                fn.close()
            with open(bfile_name, 'w') as fn:
                fn.write(contract['ContractByteCode'])
                fn.close()
            with open(afile_name, 'w') as fn:
                fn.write(contract['Address'])
                fn.close()
