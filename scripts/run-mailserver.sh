NCORE=4
for i in `seq 1 $NCORE`;
do
    echo "run-rabid $i"
    ./scripts/run-rabid.sh $i
    sleep 10
done    

for i in `seq 1 $(( $NCORE / 2 ))`;
do
    echo "run-postal-rabid $i"
    ./scripts/run-postal-rabid.sh $i
    sleep 10
done    
