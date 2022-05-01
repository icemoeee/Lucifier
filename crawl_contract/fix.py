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
filepath = "./bugs/sailfish_tod/"

# ./address/sailfish.dao.tn
# ./address/sailfish.dao.fp
# ./address/sailfish.dao.tp
# ./address/sailfish.dao
# ./address/sailfish.tod
contracta = ""
with open('./address/fix', 'r', encoding='utf-8') as dataset:
    contracta = dataset.read()

url_source = "https://api.etherscan.io/api?module=contract&action=getsourcecode&address=" + contracta + "&apikey=EY69UKAXR8IC4BUDFRM2TZ5R8V939CCI9U"
url_byte = "https://eth.tokenview.com/api/eth/contractByteCode/" + contracta
contract = {}
source = json.loads(get_content(url_source))['result'][0]
bytecode = json.loads(get_content(url_byte))['data']['contractByteCode']
contract['ContractName'] = source['ContractName']
contract['Address'] = contracta
contract['SourceCode'] = source['SourceCode']
contract['CompilerVersion'] = source['CompilerVersion']
contract['EVMVersion'] = source['EVMVersion']
contract['ContractByteCode'] = bytecode

filename = filepath + str(27)
with open(filename, 'r+') as c:
    contractj = json.load(c)
    contractj.insert(23, contract)

with open(filename, 'w+') as c:
    contract_json = json.dumps(contractj)
    c.write(contract_json)
