#!/usr/bin/python

import sys

args = []
for arg in sys.argv:
	args.append(arg)

log_file = open(args[1], "rU")
lines = log_file.readlines()

total_run = 0
run_count = 0
success_count = 0
failure_count = 0
timeout_count = 0
expt = ''
timeout_flag = False

for ll in lines:
	line = ll.strip('\t').strip().rstrip('\n')

	if line.startswith('Start'):
		line_tokens = line.split()
		expt = line_tokens[-1]
		total_run = int(line_tokens[1])
		run_count = 0
		#print "Start here"
		continue

	if line.startswith(expt):
		#print "New run"
		run_count += 1
		curr_run = int(line.split()[-1])
		assert run_count == curr_run

		if timeout_flag: # timeout
			timeout_count += 1
		else: # success or fail
			timeout_flag = True
	else:
		#print "Here?"
		if 'Assertion' in line and 'failed' in line:
			failure_count += 1
			timeout_flag = False
		elif 'successful' in line:
			success_count += 1
			timeout_flag = False
if timeout_flag:
	timeout_count += 1

assert run_count == total_run
assert success_count + failure_count + timeout_count == total_run

print expt + " results: "
print "Success: " + str(success_count) + " (rate: " + str(float(success_count)/total_run) + ")" 
print "Failure: " + str(failure_count) + " (rate: " + str(float(failure_count)/total_run) + ")" 
print "Timeout: " + str(timeout_count) + " (rate: " + str(float(timeout_count)/total_run) + ")" 

log_file.close()
