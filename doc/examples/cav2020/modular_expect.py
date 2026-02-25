import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawnu('./{}'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('foo.ub(42)')
        child.expect('= 42')
        child.expect('>')
        child.sendline('foo.ub(7)')
        child.expect('= 42')
        return True
    except pexpect.EOF:
        print (child.before)
        return False
