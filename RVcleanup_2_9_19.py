# -*- coding: utf-8 -*-
'''
Created on Fri Apr 13 23:06:41 2018

@author: Robert Ronan
Rlronan@gmail.com
Rronan1@cuny.gc.edu

'''
# RV INDUCTION IN Z^N
# LAST EDIT 2/12/19


# Iterates the dynamic system of a Rauzy-Veech Induction (on an interval exchange transformation)
# EXCEPT: The program is for studying non-Archimdian length (functions),  
# NOT subintervals with real lengths. Sage has a program for that. 
# For info on RV-Inductions see: 
# "Dynamics and geometry of the Rauzy–Veechinduction for quadratic differentials" CORENTIN BOISSY and ERWAN LANNEAU
# "Interval exchange maps and translation surfaces" Yoccoz
# "INTERVAL EXCHANGE TRANSFORMATIONS" DELECROIX
# For info on non-Archimedian lengths see Wikipedia and for theoretical fodnation of this program see:
# Kharlampovich's 2012 talk "Actions, length functions, and non-Archimedean words"  http://web.stevens.edu/algebraic/GTH/Files/Kharlampovich_talk.pdf
    

import os
import sys
import string
import copy
import csv
import argparse
import time
import random
import numpy as np
from itertools import permutations
from itertools import chain
import sympy
from sympy import symbols

subint = ''                    #String containing the name of the subintervals
lengths = []            #list containing sublists associated with each inteval
pi_0 = []                #list of order of the letters before they are permuted
pi_1 = []                #list of order of the letters after they are permuted
pi_RV=[]            #a list that keeps track of the pairs pi_0, pi_1 over time
num_iterations = 0           #the number of iterations that has occured so far
alphabet= string.ascii_uppercase   #string of the alphabet; to create subint

# The following variables are pulled from an input file if used:
file_ex_num = []                   # The example number 
file_num_int = []                  # The number of intervals (should be able to rewrte to make this implicit)
file_int_dim = []                  # The dimension (i.e. number of components) of the intervals
file_len = []                      # The touples of numerical values that correspond to the lengths of each interval
file_subint_2= []                  # The permutation that ABC..N is sent to  
# ----------------------------------------------------

runtimes = []                      # A list to hold the runtime of each example
timestamps =[]                     # A list containing time stamps used to generate runtimes
has_header = False                 # Does the output csv file alerady have a header row. Lets assume no
halt_has_header = False            # Does the halting output csv file alerady have a header row. Lets assume no
print_only = False                 # If True output is printed in console not written to file

# a CSV dialect for input files which declares how they are formatted. Using 
# the standard deliminator, comma, overly complicates deauing with the commas that seperate length components
csv.register_dialect('rv_program_dialect', delimiter='|', escapechar = '#', skipinitialspace=True, quoting=csv.QUOTE_NONE)

# the CSV dialect for the output. Currenty uses commas because many programs don't accept other delims.
csv.register_dialect('dialect', delimiter=',', escapechar = '|', skipinitialspace=True, quoting=csv.QUOTE_MINIMAL, lineterminator = '\n')

# the CSV dialect for the halt_output. Currenty uses commas because many programs don't accept other delims.
csv.register_dialect('halt_dialect', delimiter=',', escapechar = '|', skipinitialspace=True, quoting=csv.QUOTE_MINIMAL, lineterminator = '\n')



# A dictionary used to hold values which is not implemented. 
#results ={
#        'winner': '',
#        'loser': '',
#        'next winner': '',
#        'next loser': '',
#        'infinitely longer': 'False'
#        }


#def relation_solver(winner):
#    a, b, c, d = symbols('A B C D')
#    i = 0
#    x = ''
#    while i < len(winner):
#        if winner[i] == 'top':
#            x += '{} > {}, '.format(pi_RV[2*i][-1], pi_RV[2*i+1][-1])
#            i += 1
#        else:
#            x += '{} > {}, '.format(pi_RV[2*i+1][-1], pi_RV[2*i][-1])
#            i += 1
#    return x


def build_perms(num_intervals):
    print('Building permutations...')
    letters = ''
    new_element = []
    perms = []
    
    for i in range(num_intervals):
        letters += alphabet[i]
        all_perms = list(permutations(letters))    
    
    for element in all_perms:
        new_element.append(''.join(x for x in element))
    
    all_perms = new_element
    
    for i in range(len(all_perms)):
        if all_perms[i][0] == 'A':
            continue
        elif all_perms[i][-1] == letters[-1]:
            continue
        else:
            perms.append(all_perms[i])
    
    print('Permutations constructed.')
    return perms
#==============================================================================


def build_examples(num_ints, int_dim, c_vals, perms, num_exs):
    print('Building {} random examples...'.format(num_exs))
    examples = []
    #count = 0
    for q in range(num_exs):
        lengths_temp = [] 
        for interval in range(num_ints):
            lengths_temp.append((
                    ','.join(
                            map(lambda x: str(x),
                                ([random.randint(c_vals[0], c_vals[1]), 
                                  random.randint(c_vals[2], c_vals[3]), 
                                  random.randint(c_vals[4], c_vals[5])
                                  #,random.randint(c_vals[6], c_vals[7])
                                  ]))
                                )))


        lengths = ' '.join(i for i in lengths_temp)
            #i4 = random.randint(1, 100)
            #i5 = random.randint(-100, 100)
            #i6 = random.randint(-100, 100)
        
            #i7 = random.randint(1, 100)
            #i8 = random.randint(-100, 100)
            #i9 = random.randint(-100, 100)
        
            #i10 = random.randint(1, 100)
            #i11 = random.randint(-100, 100)
            #i12 = random.randint(-100, 100)
               
            
        index = q % len(perms)
        examples.append([num_ints, int_dim, perms[index], lengths])
    print('Random examples built.')
    return examples
#==============================================================================


def _add_1():
    #global file_lengths
    #global subint
    changed=False
    for i in range(1000):
        if all((file_lengths[letter][0] + file_lengths[letter][1] > 0 ) for letter in range(len(subint))):
        #print('file_lengths {},{} component {} {} component {}'.format(last_top, last_bot, 0, '+', 1))
            for letter in range(len(subint)):
                file_lengths[letter][0] += file_lengths[letter][1]
            changed = True
    return changed


def _sub_1():
    #global file_lengths
    changed=False
    for i in range(1000):
        if all((file_lengths[letter][0] - file_lengths[letter][1] > 0 ) for letter in range(len(subint))):
        #print('file_lengths {},{} component {} {} component {}'.format(last_top, last_bot, 0, '-', 1))
            for letter in range(len(subint)):
                file_lengths[letter][0] -= file_lengths[letter][1]
            changed = True
    return changed


def _add_2(): #lengths, top_idx, bot_idx, last_top, last_bot):
    #global file_lengths
    changed=False
    for i in range(1000):
        if all((file_lengths[letter][0] + file_lengths[letter][2] > 0 ) for letter in range(len(subint))):
        #print('file_lengths {},{} component {} {} component {}'.format(last_top, last_bot, 0, '+', 2))
            for letter in range(len(subint)):
                file_lengths[letter][0] += file_lengths[letter][2]
            changed = True
    
    return changed


def _sub_2(): #lengths, top_idx, bot_idx, last_top, last_bot):
    #global file_lengths
    changed=False
    for i in range(1000):
        if all((file_lengths[letter][0] - file_lengths[letter][2] > 0 ) for letter in range(len(subint))):
            for letter in range(len(subint)):
                file_lengths[letter][0] -= file_lengths[letter][2]
            changed = True
    
    return changed

function_list = [( _add_2(), _add_1(), _sub_1(), _sub_2() ), \
                 (_add_2(), _add_1(), _sub_2(), _sub_1()), \
(_add_2(), _sub_1(), _add_1(), _sub_2()), \
(_add_2(), _sub_1(), _sub_2(), _add_1()), \
(_add_2(), _sub_2(), _add_1(), _sub_1()), \
(_add_2(), _sub_2(), _sub_1(), _add_1()), \
(_add_1(), _add_2(), _sub_1(), _sub_2()), \
(_add_1(), _add_2(), _sub_2(), _sub_1()), \
(_add_1(), _sub_1(), _add_2(), _sub_2()), \
(_add_1(), _sub_1(), _sub_2(), _add_2()), \
(_add_1(), _sub_2(), _add_2(), _sub_1()), \
(_add_1(), _sub_2(), _sub_1(), _add_2()), \
(_sub_1(), _add_2(), _add_1(), _sub_2()), \
(_sub_1(), _add_2(), _sub_2(), _add_1()), \
(_sub_1(), _add_1(), _add_2(), _sub_2()), \
(_sub_1(), _add_1(), _sub_2(), _add_2()), \
(_sub_1(), _sub_2(), _add_2(), _add_1()), \
(_sub_1(), _sub_2(), _add_1(), _add_2()), \
(_sub_2(), _add_2(), _add_1(), _sub_1()), \
(_sub_2(), _add_2(), _sub_1(), _add_1()), \
(_sub_2(), _add_1(), _add_2(), _sub_1()), \
(_sub_2(), _add_1(), _sub_1(), _add_2()), \
(_sub_2(), _sub_1(), _add_2(), _add_1()), \
(_sub_2(), _sub_1(), _add_1(), _add_2())]





function_list_2 = [(_add_1(), _add_2()), \
 (_add_1(), _sub_2()), \
 (_add_2(), _add_1()), \
 (_add_2(), _sub_1()), \
 (_sub_1(), _add_2()), \
 (_sub_1(), _sub_2()), \
 (_sub_2(), _add_1()), \
 (_sub_2(), _sub_1())]


def alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot):
    #global file_lengths
    unaltered = False
    #inputs = [lengths, top_idx, bot_idx, last_top, last_bot]
    fl = function_list
    changed = False
    #fl_2 = function_list_2
    
    #changed_0 = fl_2[it_val_2][0]
    #changed_1 = fl_2[it_val_2][1]
    
    #changed = changed_0 or changed_1
    k = 0
    while not changed:
        print(k)
        if k == 4:
            break
        else:
            changed = fl[it_val_2][k]
            k += 1 
            print('changed: {}'.format(changed))
    if changed is False:
        #print('No components to combine')
        unaltered = True
    lengths = copy.deepcopy(file_lengths)
    return lengths, unaltered
            
            
#==============================================================================

def lex_longer(A, B):
    # lexagraphically compares the lengths of A and B. Returns equal if A=B,
    # top if A > B. and bot if B > A
    i = 0
    
    # We compare the lengths of each component (if neccessary)
    while i < len(A): 
        if A[i] == B[i]:
            i += 1
            if i == len(A):  # If every component is equal the lengths are equal
                return 'equal'
        elif A[i] > B[i]:
            return 'top'
        elif B[i] > A[i]:
            return 'bot'
        else:
            # Only calls on a CRITICAL ERROR. At least one of the components 
            # is not a number! Most likely the input (file) was misformatted, 
            # or missing data. 
            print 'CRITICAL ERROR: failed to compare interval lengths: {}  &  {}'.format(A,B)
            print 'an interval contains a non-numeric component.'
            print 'Most likely the input (file) was misformatted, or missing data.'
            print 'Were the number of intervals and their dimension included?'
            print ''
            print 'ERROR DATA:'
            print 'Type(first interval input) = {0} '.format(type(A))
            print 'Type(second interval input) = {0} '.format(type(B))
            print 'Lengths: {}'.format(lengths)
            print 'Pi_RV: {}'.format(pi_RV)
            print 'Pi_0: {}'.format(pi_0)
            print '#######################################################################'
            #measure_runtime += (time.time()-measure_time)
            write_output('CRITICAL ERROR: Non-numeric value', '' '', '')
            sys.exit()


def lex_subtract(A, B):
    # Subtracts B from A, componentwise. Faster than Numpy for ~ < 100 components
    c= [x - y for x,y in zip(A,B)]
    return c
    

def infinite_longer(A,B):
    # Compares intervals A, B, and return True if A is infintely larger than B
    # measure with lex-order.
    # Currently a seperate program from lex_longer because it is called after intervals
    # are measure then subtracted, and would add useless computation to lex_longer,
    # but should probably reimpliment them as one functon
    
    i = 0
    while i < len(A):
        
        if A[i] == B[i] and A[i] == 0:
            # If the i'th component of A and B are 0 then 
            # we proceed to the next component to check, and note that we've seen a zero previously.
            i += 1
            
        elif A[i] == B[i]:
            # If the i'th component of A and B are equal and non-zero,
            # then A cannot be infinitely larger, because they are comparable
            return False
        elif A[i] > 0 and B[i] <= 0:          
            return True
        elif A[i] > B[i]:
            return False
        elif B[i] > A[i]:
            return False
        else:
            # Only calls on a CRITICAL ERROR. At least one of the components 
            # is not a number! Most likely the input (file) was misformatted, 
            # or missing data. 
            print 'CRITICAL ERROR: failed to compare interval lengths: {}  &  {}'.format(A,B)
            print 'an interval contains a non-numeric component.'
            print 'Most likely the input (file) was misformatted, or missing data.'
            print 'Were the number of intervals and their dimension included?'
            print ''
            print 'ERROR DATA:'
            print 'Type(first interval input) = {0} '.format(type(A))
            print 'Type(second interval input) = {0} '.format(type(B))
            print 'Lengths: {}'.format(lengths)
            print 'Pi_RV: {}'.format(pi_RV)
            print 'Pi_0: {}'.format(pi_0)
            print '#######################################################################'
            write_output('CRITICAL ERROR: Non-numeric value', '', '', '')
            sys.exit()


def write_output(end_condition, lengths, pi_RV, winner):
    # Function to call when the iteration reaches a point where we can determine
    # the future iterations, reach maximum iterations, or run into an error.
    global has_header       # Variable holding info on whether we've written a header yet
    global halt_has_header  # Variable holding info on whether we've written a header yet
    global halt_count
    

    #halting_condition = (only_halting_inputs == 'yes') or (only_halting_inputs == 'true')

    if (end_condition == 'Ends') \
        or (end_condition == 'Unalterable') \
        or (end_condition == 'Failure') \
        or (end_condition == 'Immediate_failure'):
            end_condition_altered = 'Ends'
    else:
        end_condition_altered = end_condition
    
    if end_condition_altered == 'Ends':
        halt_count += 1
        
        if halt_has_header == False:
        #    #halt_fieldnames = ['{}/ # EX'.format(filename_input)]
            halt_fieldnames = ['EXAMPLE_NUMBER']     #'LENGTH_COMPONENTS', 'PERMUTATION', 'FINAL_LENGTHS','END_CONDITION','ITERATIONS']
            
            for letter in subint:
                for i in range(1, int_dim + 1):  
                    halt_fieldnames.append('{}{}'.format(letter, i))
            
            halt_fieldnames.append('PERMUTATION')
            for letter in subint:
               for i in range(1, int_dim + 1):
                   halt_fieldnames.append('{}{}\''.format(letter, i))
                   
            halt_fieldnames.extend(['END_CONDITION','ITERATIONS', 'RANK', 'END_RANK'])
            halt_writer.writerow(halt_fieldnames)
            halt_has_header = True
            
        halt_output_file_lengths = list(chain(*file_lengths))    #list(map(tuple, file_lengths))     
        halt_output_lengths = list(chain(*lengths))     #list(map(tuple, lengths))    
        #).strip('[]')
        
        halt_write_data = [file_example_number]
    
        for item in halt_output_file_lengths:
            halt_write_data.append(item)
        
        halt_write_data.append(file_permutation)
        
        for item in halt_output_lengths:
            halt_write_data.append(item)
        
        #halt_pi_RV = []
        #j = 0
        #while j < (len(pi_RV)):
            #print j
        #    halt_pi_RV.extend([pi_RV[j], pi_RV[j + 1]])
        #    j += 2
        
        end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
        halt_write_data.extend([end_condition, num_iterations, file_matrix_rank, end_matrix_rank]) #, str(halt_pi_RV).strip(' '), str(winner).strip(' ')])
        halt_writer.writerow(halt_write_data)
            
    if write_all is True:    
        output_file_lengths = list(chain(*file_lengths))
        output_lengths = list(chain(*lengths)) 
    
        if has_header == False:
            # verbose output is True if "include lengths" was yes.
            if verbose is True:   #.lower() == ('yes' or 'y' or 'true'):
                fieldnames = ['EXAMPLE_NUMBER'] #, 'LENGTH_COMPONENTS', 'PERMUTATION', 'FINAL_LENGTHS', 'END_CONDITION', 'ITERATIONS']
                
                for letter in subint:
                    for i in range(1, int_dim + 1):
                        fieldnames.append('{}{}'.format(letter, i))
            
                fieldnames.append('PERMUTATION')
            
                for letter in subint:
                    for i in range(1, int_dim + 1):    
                        fieldnames.append('{}{}\''.format(letter, i))
                
                
                fieldnames.extend(['END_CONDITION', 'ITERATIONS','RANK', 'END_RANK'])
                
                writer.writerow(fieldnames)
                
            else: 
                fieldnames = ['EXAMPLE_NUMBER', 'PERMUTATION', 'END_CONDITION', 'ITERATIONS', 'RANK', 'END_RANK']
                writer.writerow(fieldnames)
            has_header = True
        if verbose is True: #.lower() == ('yes' or 'y' or 'true'):

            write_data = [file_example_number,]
                 
            for item in output_file_lengths:
                write_data.append(item)
    
            write_data.append(file_permutation)
    
            for item in output_lengths:
                write_data.append(item)
            
            end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
            write_data.extend([end_condition, num_iterations, file_matrix_rank, end_matrix_rank])
            
            writer.writerow(write_data)
            
        else:
            end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
            write_data = [file_example_number, file_permutation, end_condition, num_iterations, file_matrix_rank, end_matrix_rank]
            
            writer.writerow(write_data)
        


#     MAIN FUNCTION: 
def iterate(num_intervals, int_dimension, lengths, subint, subint_2, inductions):
    # Iterates the dynamic system of a Rauzy-Veech Induction (on an interval exchange transformation)
    # For intervals with 'lengths' in Z^n ordered lexicographically. See top for more info
    pi_0 = []                #list of order of the letters before they are permuted
    pi_1 = []                #list of order of the letters after they are permuted
    pi_RV = []
    
    global num_iterations
    # build a string of letters for the intervals.
    for i in range(num_intervals):
        pi_0.append(subint[i])
    # build pi_1
    for i in range(len(subint_2)):
        pi_1.append(subint_2[i])
    #pu_RV is a record of all of our previous top and bottom permutations
    num_iterations = 0
    pi_RV.append(copy.deepcopy(pi_0))
    pi_RV.append(copy.deepcopy(pi_1))
    winner =[]

    if ((inductions == True) or (str(inductions) == 'infinity') or (str(inductions) == 'inf')):
        k = 1000000
    else:
        k = int(inductions)
    ex_prev = list(range(1000))
    for j in range(k + 1):
        
        exit_status = 0
        if j == k:
            # More than the maximum specified num of iterations are requried.
            
            write_output('UNFINSHED', lengths, pi_RV, winner)
            return
        
# The induction process itself:
        
        
        
        # Get last (right-most) element of the top and bottom permutations:
        last_top = pi_0[-1]
        last_bot = pi_1[-1]

        # Get the index of those elements in the alphabet
        # since the list contaiing lengths is in alaphebtical order
        # those indexes will work for that list:
        top_idx = alphabet.index(last_top)
        bot_idx = alphabet.index(last_bot)

        #print 'Is {0}  > {1}? Checking'.format(last_top, last_bot)
        longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])

        if longer_interval == 'equal':
            # If the two compared intervals are the same length the induction ends.
            #ind_runtime += (time.time()-ind_time)
            write_output('Ends', lengths, pi_RV, winner)
            exit_status = 1

            #print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
            #print('rerunning_halted_example')
            
            #Results of iteration:
            #print ''
            #print 'Results: '
            #print 'Example number: {}'.format(file_example_number)
            #print 'Pi_0: {0}'.format(pi_0)
            #print 'Pi_1: {0}'.format(pi_1)
            #try:
            #    print 'Last Winner: {0}'.format(winner[-1])
            #except IndexError:
            #    print 'Last Winner: None'
            #print 'File lengths of {0} = {1}'.format(subint, file_lengths)
            #print 'Lengths of {0} = {1}'.format(subint,lengths)
            #print 'Num iterations {}'.format(num_iterations)
            
            #resetting lengths (adding second component to first if positive)
            
            #if True attempts to restart the induction process from the beginning with lengths alterted by add/subtracting
            # every intervals 2nd, or 3rd, etc., component from the first. A prioiri this perserves relationships
            # and appears to work sometimes. 
            if False: 
                exit_status = 0

                #alter the lengths 1st attempt
                lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)
                
                #were the not-altered?
                if unaltered == True:
                    #print('Unalterable')
                    write_output('Unalterable', lengths, pi_RV, winner)
                    
                    return
                
                #if they were compare the lengths again:
                longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])
                
                # If they're still equal, repeat the process
                if longer_interval == 'equal':
                    
                    #2nd attempt
                    lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)
                    
                    if unaltered == True:
                        return
                
                    longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])
                    
                    if longer_interval == 'equal':
                        
                        #3rd attempt:
                        lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)
                        
                        if unaltered == True:
                            return
                        
                        longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])
                        
                        #give up after 3 tries:
                        if longer_interval == 'equal':
                            #print('Failure at length change')
                            write_output('Immediate_failure', lengths, pi_RV, winner)
                            return
                
                
                #Results of iteration:
                #print ''
                #print 'Altered results: '
                #print 'Lengths of {0} = {1}'.format(subint,lengths)    
                #print('~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=')
                num_iterations = 0
                for num in range(1000):
                    if num == 999:
                        #print('Terminating tests')
                        write_output('Failure', lengths, pi_RV, winner)
                        exit_status = 1
                        break
                    elif ex_prev[num] == file_example_number:
                        continue
                    else:
                        #print('setting values')
                        ex_prev[num] = file_example_number
                        break
                 
        if exit_status == 1:
            break
        if longer_interval == 'top':
            # The top interval is longer is thus the 'winner'
            
            # Shorten top by bot
            lengths[top_idx] = lex_subtract(lengths[top_idx], lengths[bot_idx])
            # Alter the permutations acordingly:
            pi_1.remove(last_bot)
            pi_1.insert(pi_1.index(last_top) + 1, last_bot)
            # Record the new permations
            pi_RV.append(copy.deepcopy(pi_0))
            pi_RV.append(copy.deepcopy(pi_1))
            # Note the winner: 
            winner.append('top')

        elif longer_interval == 'bot':

            lengths[bot_idx] = lex_subtract(lengths[bot_idx], lengths[top_idx])
            pi_0.remove(last_top)
            pi_0.insert(pi_0.index(last_bot) + 1, last_top)
            pi_RV.append(copy.deepcopy(pi_0))
            pi_RV.append(copy.deepcopy(pi_1))
            winner.append('bot')

        # increase the count of iterations completed. 
        num_iterations += 1
        #print 'Num iterations {}'.format(num_iterations)
        #ind_runtime += (time.time()-ind_time)
        
# The RV-Induction finishes here. 
# _____________________________________________________________________________
#
# What follows below is a series of checks to determine
# if the induction will continue forever.
# We have not proved that these conditions are exhaustive, but the progammer 
# believs that to be the case.
        
        
        
# CHECK 1: 
# Check if the (new) top interval is infinitely larger than everything else:
        #global check_overcount
        #check_time = time.time()
        count = 0
        
        # if exist status is 1, we know the answer; go to next example.
        exit_status = 0
        
        #print 'checking if pi_0[-1] >>> everything'
        for x in range(num_intervals):
            #print 'x = {}'.format(x)
            if count == (num_intervals - 1):  # range(x) is {0,1,...x-1}
                # count is at the inteval index in the list we would check against, so it is num_int - 1
                # then we are at the last interval, which is the one we compare against,
                # meaning we have checked against all other intervals, so we stop,
                # b.c. it is inf. longer than every other interval.
                
                #print '{} is >>> longer than every other interval'.format(pi_0[-1])
                #print '_______________________________________________________________________'
                exit_status = 1  # Stop checking things
                #check_runtime += (time.time()-check_time)
                #check_count = 1
                write_output('{} >> all'.format(pi_0[-1]), lengths, pi_RV, winner)
                break
            elif infinite_longer(lengths[alphabet.index(pi_0[-1])], lengths[alphabet.index(pi_0[x])]):
                # pi_0 >>> than the x'th interval (in alphabetic order)
                count += 1
            else:
                # pi_0 is not(>>>) than some interval.
                #print 'no'
                break

# CHECK 2:
# Check if the (new) bottom interval is infintely large than every other interval:
        count = 0
        if exit_status == 1:
            break
        #print 'checking if pi_1[-1] >>> everything'
        for x in range(num_intervals):
            if count == (num_intervals - 1):
                #print '{} is >>> longer than every other interval'.format(pi_1[-1])
                #print '_______________________________________________________________________'
                exit_status = 1
                
                write_output('{} >> all'.format(pi_1[-1]), lengths, pi_RV, winner)
                break
            elif infinite_longer(lengths[alphabet.index(pi_1[-1])], lengths[alphabet.index(pi_1[x])]):
                count += 1
            else:
                
                break
        if exit_status == 1:
            break

       
        
        # Use this to hold truth value of whether current top >>> current bot
        top_inf_bot = infinite_longer(lengths[alphabet.index(pi_0[-1])], lengths[alphabet.index(pi_1[-1])])

        # Use this to hold truth value of whether bot >>> top
        bot_inf_top = infinite_longer(lengths[alphabet.index(pi_1[-1])], lengths[alphabet.index(pi_0[-1])])

        ## if neither of these is true we don't yet know if we are in a repeating cycle that continues infinitely;
        ## even if CHECK 3 is satisfied, if neither is true, then that doesn't determine the future.

        ## If one of the two right-most intervals is >>> than the other, we check if there is a periodic
        ## cycle of similiar situations. The one >>> larger is also the next winner.
        #print 'Check if any of the (number of intervals -1) last iterations had the same permutation'
        # Since inifite-iterating cycles can be at most (num. intervals - 1) long
        # start that far back and move forward:

        if (top_inf_bot == True               ### SHOULD DEFINITELY CLEAN THIS UP BC
            or bot_inf_top == True):          ### COMPUTATIONALLY THINGS ARE REPEATED UNNCEESSARILY BELOW AND ABOVE

            for i in reversed( range (min (num_intervals, num_iterations+1))):
              # Check i-many iterations backward for an identical pair of permutations
              # With the same winner:
                if exit_status == 1:
                    break
                ## Note that pi_RV is the list: [inital pi_0, initial pi_1, 1st pi_0, 1st pi_1, 2nd pi_0, etc.]
                ## where 1st is the result of the first premutation, and so on.

                ## We want to check if our current permutation is the same as a
                ## i'th-previous one (i-many before now)

## if the permutations are the same, we check if the winner from that induction step (top or bot)
## is the same as what will win our current state then it may be part of a periodic cycle .
## NOTE: this is  almost certainly not implimented efficently; (USE NUMPY, CLEAN UP CODE) currently this checked,
## and then if false we recalculate next_winner in the next iteration although it doens't change

                end_comparison = False

# We recheck these since we have new values post-induction:
                last_top = pi_0[-1]
                last_bot = pi_1[-1]
                top_idx = alphabet.index(last_top)
                bot_idx = alphabet.index(last_bot)
                longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])
                #print(pi_0)
                #print(pi_1)
                #print(pi_RV)
                if (
                    i > 0
                    
                    and pi_0 == pi_RV[-2*i -2]        # This is the top half the earlier permutation we're checking against
                    and pi_1 == pi_RV[-2*i -1]        # This is the bottome half
                    and winner[-i] == longer_interval # And the same interval (top or bot) won
                    ):

                    # Build up a string of the permutation in case it ends up being the correct cycle.
                    cycle = ''
                    if longer_interval == 'top':
                        cycle = cycle + '{}-{} '.format(pi_0[-1], pi_1[-1])
                    else:
                        cycle = cycle + '{}-{} '.format(pi_1[-1], pi_0[-1])


# If the perumtation and winnner i times ago is the same as now:
# we can see that for all of the induction steps inbetween, the same interval 
# (top or bot) would win now based on our current lengths, as the interval
# that won before. And if the winner in our current lengths is
# infinitely larger than the loser ( for all pairs winner and loser in the cycle)
# then we know that the sequence of permutations will allways repeat in same way
# it has for these previous i permutations; and so
# we know the induction continues forever.

                    if end_comparison == True:
                        break

                    if exit_status == 1:
                        break

                    #print 'Current value equal to iteration i = {} times ago'.format(i)

# If the above is satisfied; check if it is also satisfied for the following iterations:

                    forward_it = 1  ## how far forward from where i is to check
                    win_count = 0   ## increments the number of times our current RV-setup wins

                    while forward_it <= i:   # We have checked i-many iterations back already
                        #print 'forward it ran'

                        if end_comparison == True:
                            break

                        if win_count == (i-1):
                            write_output('{}cycle'.format(cycle), lengths, pi_RV, winner)
                            exit_status = 1
                            break


                        previous_top = pi_RV[-2*(i - forward_it) -2][-1]   ## effectively the same as last top and bottom
                        previous_bot = pi_RV[-2*(i - forward_it) -1][-1]   ## except they are relative to
                        prev_top_idx = alphabet.index(previous_top)
                        prev_bot_idx = alphabet.index(previous_bot)


                        if winner[ -(i - forward_it)] == 'top':
                            if infinite_longer( lengths[prev_top_idx], lengths[prev_bot_idx]):
                                win_count += 1     #keeping track of how often this occurs
                                forward_it += 1    # increase forward_it by 1 to look another iteration more recent
                                cycle = cycle + '{}-{} '.format(previous_top, previous_bot)
                            else:
                                ## the winner was top, but can't be sure this pattern
                                ## repeats forever because in its current state the winner is not inf larger
                                end_comparison = True

                        elif infinite_longer(lengths[prev_bot_idx],lengths[prev_top_idx]):
                            #know winner is bot because winner == top was not true
                            #so we just look to see if the winner is inf longer
                            win_count += 1
                            forward_it += 1
                            cycle = cycle + '{}-{} '.format(previous_bot, previous_top)
                        else:
                            ## the winner is bottom but in current lengths the winner would not be infinitely larger; so this i fails
                            end_comparison = True
                            break


        if exit_status == 1:
            break
            #print '_______________________________________________________________________'

    return
    # Pretty sure this stat is unreachable.
    #sys(exit)
#
# END OF CHECKING POST-INDCTION
# END OF ITERATION FOR EXAMPLE 
# =============================================================================


# Setup that runs when program is run to set options:
print ''
print ''
print 'USER INPUTS:'
print ''

def run_program(num_intervals=2, dimension=2, component_vals=[2,2], num_examples=None, max_iterations=10000, filename_input=None, only_write_halts=False, write_lengths=True):
    
    global file_lengths
    global file_permutation
    global file_example_number
    global file_matrix_rank    
    global write_all
    global halt_count
    global verbose
    global int_dim
    global subint
    write_all = not only_write_halts
    halt_count = 0
    verbose = write_lengths
    
    c_vals = component_vals
    num_ints = num_intervals
    num_exs = num_examples
    int_dim = dimension
    int_dimension = dimension
    output_directory = './output'
    
    if not os.path.exists(output_directory):
        os.makedirs(output_directory)
    
    filename_num = 0
    for j in range(1,1000):
        if not os.path.exists(output_directory + '/' + 'run_{}'.format(j)):
            os.makedirs(output_directory + '/' + 'run_{}'.format(j))
            run_dir = output_directory + '/' + 'run_{}'.format(j)
            filename_num = j
            break
        elif j == 999:
            print('Cannot make a directory to place the run output.')
            overwrite_1 = raw_input('Overwrite files in run_1: True / False ?')
            if overwrite_1 is True:
                run_dir = output_directory + 'run_1'
                filename_num = 1
            else:
                sys.exit()
        
    if filename_input is not None:
        filename = str(filename_input)
        filename_base = filename[:-4]
        filename_halt = filename_base + '_halt_{}.csv'.format(filename_num)
        if only_write_halts == False:
            filename_output = filename_base + '_output_{}.csv'.format(filename_num)
    
    if filename_input is None: 
        filename_halt = 'rv_halt_{}.csv'.format(filename_num)
        filename_output = 'rv_output_{}.csv'.format(filename_num)
        #filename_input = 'rv_input.csv'
        if num_exs == None:
            num_exs = 1000000
        permutations = build_perms(num_intervals) 
    
        if len(c_vals) < int_dimension:
            for h in int_dim - c_vals:
                c_vals.extend(c_vals[-2],c_vals[-1])
    
        examples = build_examples(num_ints, int_dim, c_vals, permutations, num_exs)

    global writer
    global halt_writer
    #global reader
    
    with open (run_dir + '/' + filename_halt, 'a+') as output_halt_file:
        halt_writer = csv.writer (output_halt_file, dialect='halt_dialect')
                
        with open(run_dir + '/' + filename_output, 'a+') as output_file:
            writer = csv.writer(output_file, dialect='dialect')
            if filename_input is not None:
                with open(filename, "r") as input_file:
                    reader = csv.DictReader(input_file, dialect='rv_program_dialect')
        
                    start = time.time()
                    #print('Running examples...')
                    
                    for row in reader:
                        file_example_number = int(row['EXAMPLE_NUMBER'].strip())
                        file_num_intervals = int(row['NUMBER_INTERVALS'].strip())
                        file_interval_dimension = int(row['INTERVAL_DIMENSION'].strip())
                        file_permutation = row['PERMUTATION'].strip().upper()
                        lengths_temp = row['LENGTH_COMPONENTS'].strip().split()
                        file_lengths = []
                        for k in lengths_temp:
                            file_lengths.append(map(int,(k.split(','))))
           
                        subint = ''                    #String containing the name of the subintervals
                        
                        num_intervals = file_num_intervals
                        int_dim = file_interval_dimension
            
                        for i in range(num_intervals):
                            subint = subint + string.ascii_uppercase[i]

                        lengths = copy.deepcopy(file_lengths)
            
                        subint_2 = copy.copy(file_permutation)
            
                        # Please do not enter lengths in Z^1, but if you do:
                        #for i in range(len(lengths)):
                        #    if type(lengths[i]) == int:
                        #        lengths[i] = [lengths[i]]
            
                        # At every 50,000th example, note how long it has taken.
                        if (file_example_number % 50000 == 0) and (file_example_number > 1):
                            timestamps.append(time.time())
                            if len(timestamps) == 1:
                                runtimes.append(timestamps[0]-start)
                                print 'Time at Example {}: '.format(file_example_number) + 'Took %.1f seconds' % (runtimes[0])
                            else:
                                runtimes.append(timestamps[-1] - timestamps[-2])
                                print 'Time at Example {}: '.format(file_example_number) + 'Took %.1f seconds ' % (runtimes[-1]) + '(%.1f minutes total)' % (sum(runtimes)/60)
            
            
            # ITERATE THE RV INDUCTION:
                        
                        iterate(num_intervals, int_dimension, lengths, subint, subint_2, max_iterations)
                    
                    
                    
            else:
                start = time.time()
                print('Running examples...')
                print('This is safe to stop at any time (last file entry will likely be broken though)')
                file_example_number = 0
                
                for row in examples:
                    file_num_intervals = row[0]
                    file_interval_dimension = row[1]
                    file_permutation = row[2]
                    lengths_temp = row[3].strip().split()
                    file_lengths = []
                    for k in lengths_temp:
                        file_lengths.append(map(int,(k.split(','))))
                       
                    subint = ''                    #String containing the name of the subintervals
                    num_intervals = file_num_intervals
                    int_dim = file_interval_dimension
        
                    for i in range(num_intervals):
                        subint = subint + string.ascii_uppercase[i]
                    
                    lengths = copy.deepcopy(file_lengths)
        
                    subint_2 = copy.copy(file_permutation)
                    
                    file_matrix_rank = np.linalg.matrix_rank(np.matrix(file_lengths))
                    
                    # At every 50,000th example, note how long it has taken.
                    if (file_example_number % 50000 == 0) and (file_example_number > 1):
                        timestamps.append(time.time())
                        if len(timestamps) == 1:
                            runtimes.append(timestamps[0]-start)
                            print 'Time at Example {}: '.format(file_example_number) + 'Took %.1f seconds' % (runtimes[0])
                        else:
                            runtimes.append(timestamps[-1] - timestamps[-2])
                            print 'Time at Example {}: '.format(file_example_number) + 'Took %.1f seconds ' % (runtimes[-1]) + '(%.1f minutes total)' % (sum(runtimes)/60)
        
        # ITERATE THE RV INDUCTION:
                    iterate(num_intervals, int_dimension, lengths, subint, subint_2, max_iterations)
                    file_example_number += 1
                            
            # After iterating all examples, print how long functions took: 
            print 'Halting examples: {}/{};  {}%'.format(halt_count, file_example_number, (halt_count//file_example_number)*100)        
            end = time.time()
            print 'Took %f seconds' % (end - start)

for _ in range(50):
    run_program(only_write_halts=False)



# Commented out print that may be useful later:

#print '======================================================================='
#print 'Autorunning Example {}'.format(example_number)
#print 'For {} iterations'.format(max_file_its)
#print ''
#print 'Number of intervals: {}'.format(num_intervals)
#print 'Interval Dimension: {}'.format(int_dimension)
#print 'Lengths of {0} = {1}'.format(subint, lengths)
#print 'Permutation: {}'.format(subint_2)
#print ''
#print '======================================================================='
#print ''
#print 'Initial conditions: '
#print 'Pi_0: {0}'.format(pi_0)
#print 'Pi_1: {0}'.format(pi_1)
#print 'Lengths of {0} = {1}'.format(subint, lengths)
#print ''
#print '_______________________________________________________________________'




# Old commented out prints of the results after iteration: 
        #Results of iteration:
        #print ''
        #print 'Results: '
        #print 'Pi_0: {0}'.format(pi_0)
        #print 'Pi_1: {0}'.format(pi_1)
        #print 'Last Winner: {0}'.format(winner)
        #print 'Lengths of {0} = {1}'.format(subint,lengths)
        #print 'Pi_RV = {}'.format(pi_RV)











"""
# OTHERWISE RUN MANUALLY:
# NOTE: THIS IS NOT PARTICULARLY WELL MAINTAINED, BUT SO FAR AS I KNOW IT WORKS: 
else:

    print 'Running manually: '
    print ''
    print_only = True
    num_intervals = input('The number of intervals: ')

    int_dimension = input('The dimension of the intervals'
                          '(i.e the number n in Z^n): ')
    for i in range(num_intervals):
        subint = subint + string.ascii_uppercase[i]

    for i in range(num_intervals):
        x = random.randint(0,13)
        y = random.randint(-10,8)
        lengths.append(input('''Comma-separated values for components of the length of {0}
              (e.g. enter: {1},{2}    for interval {0}=({1},{2}) ): '''.format(subint[i],x,y)))

    for i in range(num_intervals):
        pi_0.append(subint[i])

    subint_2 = (raw_input(subint + ' is permuted to what ordered list of letters? ')).upper().strip()

    for i in range(len(subint_2)):
        pi_1.append(subint_2[i])

    for i in range(len(lengths)):
        if type(lengths[i]) == int:
            lengths[i] = [lengths[i]]

    ind_runtime = 0
    check_runtime = 0
    write_runtime = 0
    import_runtime = 0
    subtract_runtime = 0
    measure_runtime = 0
    inf_runtime = 0
    
    
    
    print ''
    print '======================================================================='
    print 'Please enter the following command with a numerical value to run that'
    print 'number of iterations, or with True to run indefinitely:   iterate(#) '
    print ''
    print '======================================================================='
    print ''
    print 'Initial conditions: '
    print 'Pi_0: {0}'.format(pi_0)
    print 'Pi_1: {0}'.format(pi_1)
    print 'Lengths of {0} = {1}'.format(subint, lengths)
    print ''
    print '_______________________________________________________________________'
    
# Use "iterate(number)" to run the function on your example. Currently only 
# accepts one example before needs to restarted. 
    """