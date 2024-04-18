#!/bin/bash

LOGS_DIR=logs

mkdir $LOGS_DIR

LOG_SAFE=equiv.log
LOG_UNSAFE=inequiv.log
LOG_MISC=misc.log

DFS=dfs_
BFS=bfs_
STDOUT=out_
STDERR=err_
FILES=files_
STATUS=status_

DFS_SAFE=$STDOUT$DFS$LOG_SAFE
DFS_UNSAFE=$STDOUT$DFS$LOG_UNSAFE
DFS_MISC=$STDOUT$DFS$LOG_MISC
BFS_SAFE=$STDOUT$BFS$LOG_SAFE
BFS_UNSAFE=$STDOUT$BFS$LOG_UNSAFE
BFS_MISC=$STDOUT$BFS$LOG_MISC

FILES_DFS_SAFE=$FILES$DFS$LOG_SAFE
FILES_DFS_UNSAFE=$FILES$DFS$LOG_UNSAFE
FILES_DFS_MISC=$FILES$DFS$LOG_MISC
FILES_BFS_SAFE=$FILES$BFS$LOG_SAFE
FILES_BFS_UNSAFE=$FILES$BFS$LOG_UNSAFE
FILES_BFS_MISC=$FILES$BFS$LOG_MISC

TIMES_DFS_SAFE=$STDERR$DFS$LOG_SAFE
TIMES_DFS_UNSAFE=$STDERR$DFS$LOG_UNSAFE
TIMES_DFS_MISC=$STDERR$DFS$LOG_MISC
TIMES_BFS_SAFE=$STDERR$BFS$LOG_SAFE
TIMES_BFS_UNSAFE=$STDERR$BFS$LOG_UNSAFE
TIMES_BFS_MISC=$STDERR$BFS$LOG_MISC

STATUS_DFS_SAFE=$STATUS$DFS$LOG_SAFE
STATUS_DFS_UNSAFE=$STATUS$DFS$LOG_UNSAFE
STATUS_DFS_MISC=$STATUS$DFS$LOG_MISC
STATUS_BFS_SAFE=$STATUS$BFS$LOG_SAFE
STATUS_BFS_UNSAFE=$STATUS$BFS$LOG_UNSAFE
STATUS_BFS_MISC=$STATUS$BFS$LOG_MISC

PROGRAMS_ROOT=programs

UNSAFE_PATH=$PROGRAMS_ROOT/inequiv
SAFE_PATH=$PROGRAMS_ROOT/equiv
MISC_PATH=$PROGRAMS_ROOT/misc

RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
DEFAULT='\033[0m'



declare -A SPECIAL_BOUNDS

SPECIAL_BOUNDS=(
    ["arrays.bils"]="20"
    ["rivcp-4.1.2-e.bils"]="36"
    ["ex4v2-ineq.bils"]="7"
    ["ex4v3-ineq.bils"]="10"
    ["ex4v4-ineq.bils"]="13"
    ["ex4v5-ineq.bils"]="16"
    ["syteci-fact-e.bils"]="6"
    ["bsearch-eq-1.bils"]="20" #too hard to solve? (tested up to 500)
    ["bsearch-eq-2.bils"]="22" #too hard to solve? (tested up to 500)
    ["bsearch-eq-3.bils"]="21" #too hard to solve? (tested up to 500)
    ["bsearch-ineq-1.bils"]="9" 
    ["bsearch-ineq-2.bils"]="11"
    ["bsearch-ineq-3.bils"]="17"
    ["bsearch-ineq-4.bils"]="18"
    ["bsearch-ineq-5.bils"]="18"
    ["call-nested-param.bils"]="102"
    ["cross-reentrancy-param.bils"]="202"
    ["cross-reentrancy-param-v2.bils"]="9"
    ["cross-reentrancy-param-v3.bils"]="9"
    ["pdnf_event-handler_button-counter.bils"]="208"
    ["pdnf_event-handler_DOM-image-load.bils"]="19"
    ["pdnf_event-handler_edit-text.bils"]="21"
    ["pdnf_event-handler_JavaSwing-mouse-pos.bils"]="20"
    ["pdnf_event-handler_jQuery-toggle.bils"]="9"
    ["pdnf_event-handler_form-validation.bils"]="20"
    ["pdnf_event-handler_keypress.bils"]="20"
    ["pdnf_event-handler_keypress_finalmethod.bils"]="22"
    ["pdnf_event-handler_onclick.bils"]="12"
    ["pdnf_event-handler_onclick.bils-2"]="12"
    ["pdnf_event-handler_timer.bils"]="26"
    ["holik-file-lock-param-e-large.bils"]="101"
    ["holik-file-lock-param-e.bils"]="33"
    ["holik-flat-combiner-e.bils"]="7"
    ["holik-reentrancy-e3.bils"]="61"
    ["holik-flat-combiner-v2-e.bils"]="7" #blows up too much to analyse
    ["holik-flat-combiner-v4-e.bils"]="5" #blow up too much to analyse
    ["hector-bsort-CN5-sorted.bils"]="167"
    ["hector-bsort-isort-CN2-one-step.bils"]="25"
    ["hector-bsort-isort-CN5-one-step.bils"]="39"
    ["hector-bsort-isort-CN10-one-step.bils"]="64"
    ["hector-bsort-isort-CN10-all-steps.bils"]="20"
    ["hector-bsort-isort-CN100-all-steps.bils"]="20"
    ["hector-bsort-isort-CNE.bils"]="17"
    ["hector-isort-CN5.bils"]="111"
    ["hector-bsort-isort-CN2.bils"]="34"
    ["hector-bsort-isort-CN5.bils"]="79"
    ["hector-bsort-isort-CN10.bils"]="154"
    ["hector-kierstead.bils"]="7"
    ["hector-pitts-stark.bils"]="9"
    ["hector-thamsborg.bils"]="22"
    ["invariants-1.bils"]="13"
    ["invariants-4.bils"]="5"
    ["invariants-4-v2.bils"]="15"
    ["invariants-4-v3.bils"]="9"
    ["pitts-3.14.bils"]="29"
    ["pdnf_protocol_telecoms-handover.bils"]="32"
    ["identity-2.bils"]="12"
    ["meyer-sieber-e4v2-fin.bils"]="66"
    ["meyer-sieber-e5v2-fin.bils"]="104"
    ["meyer-sieber-e6.bils"]="10"
    ["meyer-sieber-e6v2.bils"]="10"
    ["meyer-sieber-ineq.bils"]="9"
    ["meyer-sieber-e5v2-outerref.bils"]="6"
    ["reve-barthe-ineq.bils"]="15"
    ["reve-limit2-ineq.bils"]="12"
    ["reve-nested-while.bils"]="8"
    ["sigma-gc-equiv.bils"]="8"
    ["state-dependent-2.bils"]="9"
    ["state-dependent-4.bils"]="7"
    ["state-dependent-4v2.bils"]="16"
    ["stateful-args-eq-2.bils"]="6"
    ["stateful-args-eq-3.bils"]="6"
    ["stateful-args-eq.bils"]="6"
    ["syteci-call-lock.bils"]="10"
    ["syteci-cwl.bils"]="7"
    ["syteci-well-bracket-state.bils"]="22"
    ["syteci-iterator-unfold.bils"]="7"
    ["syteci-well-bracket-dummy.bils"]="7"
    ["syteci-isc.bils"]="9"
    ["list-qsort-N5_encoded.bils"]="234"
    ["list-msort-N5_encoded.bils"]="251"
    ["list-qsort-N6_encoded.bils"]="338"
    ["list-msort-N6_encoded.bils"]="353"
    ["list-qsort-msort-N5_encoded.bils"]="245"
    ["list-qsort-N5_built-in.bils"]="70"
    ["list-msort-N5_built-in.bils"]="45"
    ["list-qsort-N6_built-in.bils"]="99"
    ["list-msort-N6_built-in.bils"]="60"
    ["list-msort-N5-ineq.bils"]="27"
    ["list-qsort-N5-ineq.bils"]="27"
    ["syteci-call-lock.bils"]="1"
    ["syteci-rep-ind.bils"]="1"
    ["qsort-isort-N100.bils"]="76"
    ["gc-equiv-2.bils"]="7"
    ["gc-equiv.bils"]="7"
    ["nr-equiv-state.bils"]="12"
    ["nt-050723-1153.bils"]="10"
    ["vk-280222-2.bils"]="10"
    ["vk-Aug10-1755.bils"]="8"
    ["vk-arrays-ineq.bils"]="6"
    ["yy_17-feb-23_6_ineq.bils"]="8"

    # temporary bounds to for things we cannot prove:

    
#    ["syteci-call-lock.bils"]="5"
#    ["syteci-rep-ind.bils"]="5"
#    ["syteci-well-bracket-state.bils"]="5"
#    ["fact-tail-rec.bils"]="5"
#    ["mccarthy.bils"]="5"
#    ["mccarthy-imp.bils"]="5"
#    ["mccarthy-knuth2.bils"]="5"
#    ["mccarthy-knuth.bils"]="5"    

)


print_check_message () {
    printf "checking ${CYAN}${BOLD}$1${DEFAULT} with bound ${CYAN}${BOLD}$2${DEFAULT}..."
}
print_header () {
    START=${#1}
    END=65
    
    printf "\n${CYAN}<><>${DEFAULT}"
    printf "${BOLD}Running $1${DEFAULT}"

    for (( c=$START; c<=$END; c=$c+2 ))
    do
        printf "${CYAN}<>${DEFAULT}"
    done
    
    printf "\n"
}
print_log () {
    printf "\n$1 result in file: ${BOLD}%s${DEFAULT}\n" $2
}

total_checked=0
eq_proved_num=0
ineq_proved_num=0
inconclusive_num=0
error_num=0

run_test () {
    print_header "$1"
    
    for file in $2/*.bils
    do
        filename=$(basename $file)
        [ ${SPECIAL_BOUNDS["$filename"]+abc} ] && BOUND=${SPECIAL_BOUNDS["$filename"]} || BOUND=6
        
        print_check_message $file $BOUND

        echo $filename >> $6
        
        OUTPUT=$((time timeout 150s ./hobbit_pdnf.native -i $file -t $4 -b $BOUND -u "$8") 2>> $5)
        EXIT_CODE=$?
        
        if [ $EXIT_CODE -eq 0 ]
        then
            echo -e "\u001b[33minconclusive\033[0m"
            echo "N/A" >> $7
            let "inconclusive_num+=1"
        elif [ $EXIT_CODE -eq 42 ]
        then
            echo -e "\033[1;33minequivalent\033[0m"
            echo "no" >> $7
            let "ineq_proved_num+=1"
        elif [ $EXIT_CODE -eq 43 ]
        then
            echo -e "\033[1;32mequivalent\033[0m"
            echo "yes" >> $7
            let "eq_proved_num+=1"
        else
            echo -e "\033[1;31merror\033[0m"
            echo "error" >> $7
            let "error_num+=1"
        fi

        let "total_checked+=1"
        
        printf "$OUTPUT\n\n\n\n"  >> $3
    done
    print_log "$1" $3
}

TIMEFORMAT=%R
#let "eq_proved_num=0"
#let "ineq_proved_num=0"
#let "inconclusive_num=0"
#let "error_num=0"
#run_test "DFS Sanity Tests" ${MISC_PATH} $DFS_MISC 1 $TIMES_DFS_MISC $FILES_DFS_MISC $STATUS_DFS_MISC
#run_test "DFS Equivalence Checks" ${SAFE_PATH} $DFS_SAFE 1 $TIMES_DFS_SAFE $FILES_DFS_SAFE $STATUS_DFS_SAFE
#run_test "DFS Inequivalence Checks" ${UNSAFE_PATH} $DFS_UNSAFE 1 $TIMES_DFS_UNSAFE $FILES_DFS_UNSAFE $STATUS_DFS_UNSAFE
#echo -e "\033[1;32m*** $(eq_proved_num) equivalences proved\033[0m"
#echo -e "\033[1;33m*** $(ineq_proved_num) inequivalences proved\033[0m"
#echo -e "\u001b[33m*** $(inconclusive_num) inconclusive examples\033[0m"
#echo -e "\033[1;31m*** $(error_num) error(s) in programs\033[0m"

run_test_arg () {
    DIR=$LOGS_DIR/$1
    
    mkdir $DIR

    rm -f $DIR/$DFS_SAFE
    rm -f $DIR/$DFS_UNSAFE
    rm -f $DIR/$DFS_MISC
    rm -f $DIR/$BFS_SAFE
    rm -f $DIR/$BFS_UNSAFE
    rm -f $DIR/$BFS_MISC

    rm -f $DIR/$FILES_DFS_SAFE
    rm -f $DIR/$FILES_DFS_UNSAFE
    rm -f $DIR/$FILES_DFS_MISC
    rm -f $DIR/$FILES_BFS_SAFE
    rm -f $DIR/$FILES_BFS_UNSAFE
    rm -f $DIR/$FILES_BFS_MISC

    rm -f $DIR/$TIMES_DFS_SAFE
    rm -f $DIR/$TIMES_DFS_UNSAFE
    rm -f $DIR/$TIMES_DFS_MISC
    rm -f $DIR/$TIMES_BFS_SAFE
    rm -f $DIR/$TIMES_BFS_UNSAFE
    rm -f $DIR/$TIMES_BFS_MISC

    rm -f $DIR/$STATUS_DFS_SAFE
    rm -f $DIR/$STATUS_DFS_UNSAFE
    rm -f $DIR/$STATUS_DFS_MISC
    rm -f $DIR/$STATUS_BFS_SAFE
    rm -f $DIR/$STATUS_BFS_UNSAFE
    rm -f $DIR/$STATUS_BFS_MISC
    
    # run_test "BFS Sanity Tests" ${MISC_PATH} $DIR/$BFS_MISC 0 $DIR/$TIMES_BFS_MISC $DIR/$FILES_BFS_MISC $DIR/$STATUS_BFS_MISC $2
    
    run_test "BFS Equivalence Checks" ${SAFE_PATH} $DIR/$BFS_SAFE 0 $DIR/$TIMES_BFS_SAFE $DIR/$FILES_BFS_SAFE $DIR/$STATUS_BFS_SAFE $2
    echo -e "\033[1;32m*** ${eq_proved_num} equivalences proved\033[0m"
    echo -e "\u001b[34;1m*** ${total_checked} files checked\033[0m"
    
    run_test "BFS Inequivalence Checks" ${UNSAFE_PATH} $DIR/$BFS_UNSAFE 0 $DIR/$TIMES_BFS_UNSAFE $DIR/$FILES_BFS_UNSAFE $DIR/$STATUS_BFS_UNSAFE $2

    echo -e "\033[1;32m*** ${eq_proved_num} equivalences proved\033[0m"
    echo -e "\033[1;33m*** ${ineq_proved_num} inequivalences proved\033[0m"
    echo -e "\u001b[33m*** ${inconclusive_num} inconclusive examples\033[0m"
    echo -e "\033[1;31m*** ${error_num} error(s) in programs\033[0m"
    echo -e "\u001b[34;1m*** ${total_checked} files checked\033[0m"

    let "eq_proved_num=0"
    let "ineq_proved_num=0"
    let "inconclusive_num=0"
    let "error_num=0"
    let "total_checked=0"
}

O_DEF="ngsrialfuh"
O_NOSEP="ngrialfzuh"
O_NORE="ngsialfzuh"
O_NOSIG="ngsrizueh"
O_NOREE="ngsrialfzu"
O_NOGEN="ngsrialfuh"
O_NONE=""

F_DEF=default
F_NOSEP=no_sep
F_NORE=no_reuse
F_NOSIG=no_sigma
F_NOGEN=no_gen
F_NOREE=no_reentry
F_NONE=no_all

run_test_arg $F_DEF $O_DEF
#run_test_arg $F_NOSEP $O_NOSEP
#run_test_arg $F_NORE $O_NORE
#run_test_arg $F_NOSIG $O_NOREE
#run_test_arg $F_NOGEN $O_NOGEN
#run_test_arg $F_NOREE $O_NOREE
#run_test_arg $F_NONE $O_NONE
