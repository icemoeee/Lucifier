#!/usr/bin/bash
declare -A Address_map
Address_map=()
AddressTotal=0
AddressCounter=0
ErrorCounter=0

base_dir="/home/doctordc/Documents/datasets/reentrancy/*"
for file in $base_dir
do
    if test -d $file
    then
        fn=`ls $file/* | grep ".sol$"`
		python oyente.py -s ${fn} -sv 0.4.25 -se -r
		re_file=`ls $file/* | grep ".report$"`
		if [[ $re_file ]]	# 没有report文件则视为报错
        then
        	fln=`wc -l $re_file | awk '{print $1}'` 
        	if [[ $fln = 0 ]]; then
        		ErrorCounter=$(($ErrorCounter+1))
				Address_map[$fn]=error
			else
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
				Address_map[$fn]=$reflag
				unset reflag
        	fi
		else
			ErrorCounter=$(($ErrorCounter+1))
			Address_map[$fn]=error
		fi
		AddressTotal=$(($AddressTotal+1))
    fi
done
# 保存结果
touch aresult.csv
echo error, $ErrorCounter >> aresult.csv
echo reentrancy, $AddressCounter >> aresult.csv
echo totalcontracts, $AddressTotal >> aresult.csv
for key in ${!Address_map[*]}; do
	echo ${key}, ${Address_map[$key]} >> aresult.csv
done
