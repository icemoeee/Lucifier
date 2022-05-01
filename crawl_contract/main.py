from get_url import *
from time_change import *
import traceback
import json
import time

# ./ground-truth/sailfish_dao_tn/
# ./ground-truth/sailfish_dao_fp/
# ./ground-truth/sailfish_dao_tp/
# ./bugs/sailfish_dao/
# ./bugs/sailfish_tod/
# ./dataset
filepath = "./dataset"

# ./address/sailfish.dao.tn
# ./address/sailfish.dao.fp
# ./address/sailfish.dao.tp
# ./address/sailfish.dao
# ./address/sailfish.tod
# ./address/dataset
datasets = []
with open('./address/dataset', 'r', encoding='utf-8') as dataset:
    lines = dataset.readlines()
    for line in lines:
        datasets.append(line.rstrip())

contracts = []
cot = 1
num = 0
start = 100 * num
size = len(datasets) - start
start_time = time.time()
for dataset in datasets[start:]:
    real = str(int(str(num * 100 + cot)))
    print(real + " " + dataset)
    url_source = "https://api.etherscan.io/api?module=contract&action=getsourcecode&address=" + dataset + "&apikey=EY69UKAXR8IC4BUDFRM2TZ5R8V939CCI9U"
    url_byte = "https://eth.tokenview.com/api/eth/contractByteCode/" + dataset
    contract = {}
    try: 
        source = json.loads(get_content(url_source))['result'][0]
        bytecode = json.loads(get_content(url_byte))['data']['contractByteCode']
        contract['ContractName'] = source['ContractName']
        contract['Address'] = dataset
        contract['SourceCode'] = source['SourceCode']
        contract['CompilerVersion'] = source['CompilerVersion']
        contract['EVMVersion'] = source['EVMVersion']
        contract['ContractByteCode'] = bytecode
        contracts.append(contract)
    except Exception:
        traceback.print_exc()
        with open(filepath + "address_error", 'a+') as e:
                e.write("Num : " + real + " " + dataset + "\n" + str(traceback.format_exc()))
        cot += 1
        continue

    if cot == 100:
        filename = filepath + str(num)
        try:
            contract_json = json.dumps(contracts)
            with open(filename, 'w+') as c:
                c.write(contract_json)
            num += 1
            cot = 0
            contracts = []
        except Exception:
            traceback.print_exc()
            with open(filepath + "write_error", 'a+') as e:
                e.write("Num : " + real + " " + dataset + "\n" + str(traceback.format_exc()))
            num += 1
            cot = 0
            contracts = []
            continue
    
    # 显示进度
    end_time = time.time()
    use_time = end_time - start_time
    rest_time = use_time * (size - int(real)) / int(real)
    use_time_str = time_change(use_time)
    rest_time_str = time_change(rest_time)
    print("进度 : %.0f%%, 用时 : %s, 剩余时间 : %s"%(int(real) / size * 100, use_time_str, rest_time_str))
    
    cot += 1
    time.sleep(0.2)

filename = filepath + str(num)
try:
    contract_json = json.dumps(contracts)
    with open(filename, 'w+') as c:
        c.write(contract_json)
except Exception:
    traceback.print_exc()
