import pexpect
import sys

def run(name,opts,res):
    child = pexpect.spawnu('./{}'.format(name))
    child.logfile = sys.stdout
    try:
        child.expect('>')
        child.sendline('account.withdraw(4)')
        child.expect('assumption failed')
        return True
    except pexpect.EOF:
        print(child.before)
        return False
