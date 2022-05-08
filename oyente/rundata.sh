#!/usr/bin/bash
declare -A Address_map
Address_map=()
AddressTotal=0
AddressCounter=0
ErrorCounter=0

# base_dir="/home/doctordc/Documents/ceshidata/*"
base_dir="/home/doctordc/Documents/tests/datasets/contracts/*"
for file in $base_dir
do
    if test -d $file
    then
    	cv_file=`ls $file/* | grep "CompilerVersion"`
        cv=`head -n1 $cv_file`
        fn=`ls $file/* | grep ".sol$"`
        if [[ -z $fn ]]
        then	# 没有源文件则用字节码
			fn=`ls $file/* | grep ".byte$"`
		fi
		ad_file=`ls $file/* | grep ".address$"`
		address=`head -n1 $ad_file`
		python oyente.py -s $fn -sv $cv -se -r
		re_file=`ls $file/* | grep ".report$"`
		if [[ $re_file ]]	# 没有report文件则视为报错
        then
        	reflag=false
			for rfile in $re_file
			do
				result=`tail -n1 $rfile`
			if [[ $result = True ]]; then
				reflag=true	# 有True则为重入
			fi
			done

			if [[ $reflag = true ]]; then
				AddressCounter=$(($AddressCounter+1))
			fi
			Address_map[$address]=$reflag
			unset reflag
		else
			ErrorCounter=$(($ErrorCounter+1))
			Address_map[$address]=error
		fi
		AddressTotal=$(($AddressTotal+1))
    fi
done
# 保存结果
touch result.csv
echo error, $ErrorCounter >> result.csv
echo reentrancy, $AddressCounter >> result.csv
echo totalcontracts, $AddressTotal >> result.csv
for key in ${!Address_map[*]}; do
	echo ${key}, ${Address_map[$key]} >> result.csv
done
