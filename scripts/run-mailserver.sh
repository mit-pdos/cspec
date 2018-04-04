SRV=$1
NCLIENT=4
for i in `seq 1 $NCLIENT`;
do
    ./scripts/mk-users.sh
    $1 &
    sleep 10
    echo "mclnt $i"
    ./gomail/mclnt $i
    kill %1
done    

