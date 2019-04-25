echo "Compiling files in _Project:"
while read F  ; do
	echo "\t" $F
    hoqc -R . "" $F
done <_Project
