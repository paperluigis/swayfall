# sway gravity
an impractical i3ipc script that makes all floating windows (that are not sticky) fall.

inspired by [another python program of a similar name](https://github.com/Failedex/SwayGravity).

it works on sway 1.10, not sure about its compatibility with i3.

the script is supposed to be run with pypy but cpython should work too


## running the thing
```console
$ # assuming that we're in a python3 venv
$ pip install -r requirements.txt
$ ./gravity.py
$ # sometimes it fails to kill its subprocesses on exit
$ killall pw-cli
```
