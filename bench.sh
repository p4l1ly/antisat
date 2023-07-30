while read -r f; do
  echo -n $f' ';

  for mode in 3 2 1 0; do
    /usr/bin/time -f '%e %S %U %P %x' \
      timeout 15 ./build/afaminisat $mode $f 2>/tmp/err.log > /tmp/out.log;
    code=$?
    if [ $code = 124 ]; then
      echo -n 'TIMEOUT '
      cat /tmp/err.log | tail -n1 | tr '\n' ' ';
    elif [ $code = 0 ]; then
      cat /tmp/out.log | tr '\n' ' ';
      cat /tmp/err.log | tr '\n' ' ';
    else
      echo -n "ERROR 0 0 0 0% $code "
    fi
  done
  echo
done
