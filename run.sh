rm tree 
cc -I . -g -o tree -DRUN main.c -lpthread
if ./tree
then
	echo successful
else
	echo FAILED
fi
