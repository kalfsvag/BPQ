echo "Compiling files in _Project:"
while read F  ; do
	echo "\t" $F
    hoqc -R src "" $F
done <_Project
