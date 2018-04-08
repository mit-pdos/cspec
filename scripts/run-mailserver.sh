NPROC=$1
NMSG=100000
N=$(($NMSG * $NPROC))
echo "== mail-test $NPROC $NMSG $N `date` == "
for i in `seq 1 $NPROC`;
do
    echo "== mail-test $i $((N / i))"
    ./scripts/mk-users.sh; time ./bin/mail-test $NPROC $((N / i)) 1 0
    sleep 10
done    

