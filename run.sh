rm tree 
cc -I . -g -o tree -DRUN -DPER_CPU_DATA_ARRAY main.c -lpthread
if ./tree
then
	echo successful
else
	echo FAILED
fi
