# -*- coding: utf-8 -*-
'''
Created on Fri Apr 13 23:06:41 2018

@author: Robert Ronan
Rlronan@gmail.com
Rronan1@cuny.gc.edu

'''
# RV INDUCTION IN Z^N
# LAST EDIT 9/26/2020 (


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

subint = ''                    #String containing the name of the subintervals
lengths = []            #list containing sublists associated with each inteval
pi_0 = []                #list of order of the letters before they are permuted
pi_1 = []                #list of order of the letters after they are permuted
pi_RV = []            #a list that keeps track of the pairs pi_0, pi_1 over time
num_iterations = 0           #the number of iterations that has occured so far
alphabet = string.ascii_uppercase   #string of the alphabet; to create subint

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




# =============================================================================
# The program runs as follows:
# 0. Permutations are built.
# 1. Examples are built.
# 2. For each example:
#   3. Iteration is run:
#     4. lex_longer is run to compare to subinterval lengths.
#     5. a) If the lengths are ==: write_output is run, and the next example begins at (2).
#     5. b) Otherwise the shorter length is subtracted from the longer length
#           and the subintervals are permuted. The number of iterations is incremented.
#     6. Checks are performed to see if the example should be halted:
#       7. Check 1: infinite_longer is run to see if the top right interval is
#                   infinitely longer than the bottom right. If so, outcome is determined,
#                   write_output is run, and the next example begins at (2).
#       8. Check 2: the same as step 7, but to see if the bottom right interval is >>> longer.
#       9. Check 3: If either the top or bottom interval is infinitely longer than
#                   the other, we check to see whether there is a sequence
#                   of permutations that will repeat cyclically due to all of the
#                   winners being >>> than the losers. If so, the outcome is determined,
#                   write_output is run, and the next example begins at (2).
#     10. Else, all checks have failed and we cannot yet determine the outcome.
#
#
# =============================================================================



# IMPLEMENTATION PROPOSALS:
# =============================================================================
# 0. Fix comments, add docstrings for all functions.
#
# 1. 'Comparamentalize' functions across files so that files are easier to read.
#
# 2. Add functionality to run program from command line.
#
# 3. Address programming inefficiencies in check 3.
#
# 4. Address repeated length comparisons in check 1, 2 and between 3.
#
# 5. Run checks with decreased frequency.
#     Notes: probably significantly faster. Easy to implement, but no longer have
#     information on exact number iterations before halt. Possibly work-aroundable.
#
# 6. Recheck code for running examples from file works.
#
# 7. Relocate proof of correctness for code.
#
# 8. Fix inconsistent usage of term 'halt.'
#
# 9. Fix debugging code.
#
# DONE: 10. Reimplement build_examples with np.random
# =============================================================================







def build_perms(num_intervals):
    #print('Building permutations...')
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

    #print('Permutations constructed.')
    return perms


def build_examples(num_ints, int_dim, c_vals, perms, num_exs):
    """
    Input:
        num_ints: the number of subintervals (int)
        int_dim: the dimension of the subintervals (int)
        c_vals: list of pairs, (lower, upper) containing lower and upper bounds for
                the values that different components/dimensions of a subinterval
                can take. (int_dim many tuples of two ints)
        perms: List of all valid permutations on num_ints many subintervals that
                examples may choose from.
        num_exs: the number of examples (int)

    Returns:
        Randomly generated (within the given bounds) examples to be run using
        the iterate function.

    Example usage:
        build_examples(4, 3, [(1,3), (-3,3), (0,5)], perms, 10)
            will return 10 examples containing intervals ABCD, where each
            interval is is in Z^{3}, and each interval has
            length: [x_1, x_2, x_3], where x_1 is in [1,3], x_2 in [-3,3],
            and x_3 in [0,5]. Interval C might, for example, have length
            [1,-1,5].
    """
    print('Building {} random examples...'.format(num_exs))
    assert type(c_vals[0]) == tuple
    if len(c_vals) < int_dim:
        print('Expected {} pairs of component values. Recieved {}: '.format(
                int_dim, len(c_vals)), c_vals)
        print("Inferring remaining pairs are identical to last pair provided.")
        for i in range(int_dim - len(c_vals)):
            c_vals.append(c_vals[-1])
    elif len(c_vals) > int_dim:
        print('Expected {} pairs of component values. Recieved {}. Ignoring last {} pairs: '.format(
                int_dim, len(c_vals), len(c_vals) - int_dim), c_vals[-(len(c_vals) - int_dim):])

    # This is faster than building the examples individually.
    rng = np.random.default_rng()

    examples = np.array(list(
      rng.integers(c_vals[dim][0], c_vals[dim][1]+1, size=(num_ints, num_exs))
      for dim in range(int_dim)))

    examples = examples.T.reshape(num_exs, num_ints, int_dim).tolist()

    permutations = rng.choice(perms, size=num_exs, replace=True)
    # examples = []
    # for q in range(num_exs):
    #     lengths = []
    #     for interval in range(num_ints):
    #         lengths.append(list(
    #           random.randint(c_vals[dim][0], c_vals[dim][1])
    #           for dim in range(int_dim)))

    #     index = q % len(perms)
    #     examples.append([num_ints, int_dim, perms[index], lengths])
    print('Random examples built.')
    return examples, permutations

def lex_longer(A, B):
    """


    Parameters
    ----------
    A : List of ints
      Length for top interval being compared.
    B : List of ints
      Length for the bottom interval being compared.

    Returns
    -------
    str

    lexagraphically compares the lengths of A and B. Returns 'equal' if A=B,
    'top' if A > B. and 'bot' if B > A
    """
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
            print('CRITICAL ERROR: failed to compare interval lengths: {}  &  {}'.format(A,B))
            print('an interval contains a non-numeric component.')
            print('Most likely the input (file) was misformatted, or missing data.')
            print('Were the number of intervals and their dimension included?')
            print('')
            print('ERROR DATA:')
            print('Type(first interval input) = {0} '.format(type(A)))
            print('Type(second interval input) = {0} '.format(type(B)))
            print('Lengths: {}'.format(lengths))
            print('Pi_RV: {}'.format(pi_RV))
            print('Pi_0: {}'.format(pi_0))
            print('#######################################################################')
            #measure_runtime += (time.time()-measure_time)
            write_output('CRITICAL ERROR: Non-numeric value', '' '', '')
            assert TypeError()
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
            print('CRITICAL ERROR: failed to compare interval lengths: {}  &  {}'.format(A,B))
            print('an interval contains a non-numeric component.')
            print('Most likely the input (file) was misformatted, or missing data.')
            print('Were the number of intervals and their dimension included?')
            print('')
            print('ERROR DATA:')
            print('Type(first interval input) = {0} '.format(type(A)))
            print('Type(second interval input) = {0} '.format(type(B)))
            print('Lengths: {}'.format(lengths))
            print('Pi_RV: {}'.format(pi_RV))
            print('Pi_0: {}'.format(pi_0))
            print('#######################################################################')
            write_output('CRITICAL ERROR: Non-numeric value', '', '', '')
            sys.exit()


def write_output(end_condition, lengths, pi_RV, winner):

    # Function to call when the iteration reaches a point where we can determine
    # the future iterations, reach maximum iterations, or run into an error.
    global has_header       # Variable holding info on whether we've written a header yet
    global halt_has_header  # Variable holding info on whether we've written a header yet
    global halt_count
    global iteration_count
    iteration_count += num_iterations
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
        if do_not_write:
          return

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

            halt_fieldnames.extend(['END_CONDITION','ITERATIONS'])#, 'RANK', 'END_RANK'])
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

       #end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
        halt_write_data.extend([end_condition, num_iterations])#, file_matrix_rank, end_matrix_rank]) #, str(halt_pi_RV).strip(' '), str(winner).strip(' ')])
        halt_writer.writerow(halt_write_data)
    if do_not_write:
        return
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


                fieldnames.extend(['END_CONDITION', 'ITERATIONS'])#,'RANK', 'END_RANK'])

                writer.writerow(fieldnames)

            else:
                fieldnames = ['EXAMPLE_NUMBER', 'PERMUTATION', 'END_CONDITION', 'ITERATIONS']#, 'RANK', 'END_RANK']
                writer.writerow(fieldnames)
            has_header = True
        if verbose is True: #.lower() == ('yes' or 'y' or 'true'):

            write_data = [file_example_number,]

            for item in output_file_lengths:
                write_data.append(item)

            write_data.append(file_permutation)

            for item in output_lengths:
                write_data.append(item)

            #end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
            write_data.extend([end_condition, num_iterations])#, file_matrix_rank, end_matrix_rank])

            writer.writerow(write_data)

        else:
            #end_matrix_rank = np.linalg.matrix_rank(np.matrix(lengths))
            write_data = [file_example_number, file_permutation, end_condition, num_iterations]#, file_matrix_rank, end_matrix_rank]

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
    #pi_RV is a record of all of our previous top and bottom permutations
    num_iterations = 0
    pi_RV.append(copy.deepcopy(pi_0))
    pi_RV.append(copy.deepcopy(pi_1))
    winner =[]

    if ((inductions == True) or (str(inductions) == 'infinity') or (str(inductions) == 'inf')):
        k = 1000000
    else:
        k = int(inductions)
    #ex_prev = list(range(1000))
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


            #resetting lengths (adding second component to first if positive)

            # if False:
            #if True attempts to restart the induction process from the beginning with lengths alterted by add/subtracting
            # every intervals 2nd, or 3rd, etc., component from the first. (NOT A prioiri) this perserves relationships
            # and appears to work sometimes.

            #     exit_status = 0

            #     #alter the lengths 1st attempt
            #     lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)

            #     #were the not-altered?
            #     if unaltered == True:
            #         #print('Unalterable')
            #         write_output('Unalterable', lengths, pi_RV, winner)

            #         return

            #     #if they were compare the lengths again:
            #     longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])

            #     # If they're still equal, repeat the process
            #     if longer_interval == 'equal':

            #         #2nd attempt
            #         lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)

            #         if unaltered == True:
            #             return

            #         longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])

            #         if longer_interval == 'equal':

            #             #3rd attempt:
            #             lengths, unaltered = alter_lengths(lengths, top_idx, bot_idx, last_top, last_bot)

            #             if unaltered == True:
            #                 return

            #             longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])

            #             #give up after 3 tries:
            #             if longer_interval == 'equal':
            #                 #print('Failure at length change')
            #                 write_output('Immediate_failure', lengths, pi_RV, winner)
            #                 return


            #     #Results of iteration:
            #     #print ''
            #     #print 'Altered results: '
            #     #print 'Lengths of {0} = {1}'.format(subint,lengths)
            #     #print('~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=')
            #     num_iterations = 0
            #     for num in range(1000):
            #         if num == 999:
            #             #print('Terminating tests')
            #             write_output('Failure', lengths, pi_RV, winner)
            #             exit_status = 1
            #             break
            #         elif ex_prev[num] == file_example_number:
            #             continue
            #         else:
            #             #print('setting values')
            #             ex_prev[num] = file_example_number
            #             break

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

# One step of the RV-Induction finishes here.
# _____________________________________________________________________________
#
# What follows below is a series of checks to determine
# if the induction will continue forever.
#TODO: I thought I did prove that. Double check.
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
            if count == (num_intervals - 1):  # range(x) is {0,1,...x-1}
                # count is at the inteval index in the list we would check against, so it is num_int - 1
                # then we are at the last interval, which is the one we compare against,
                # meaning we have checked against all other intervals, so we stop,
                # b.c. it is inf. longer than every other interval.

                #print '{} is >>> longer than every other interval'.format(pi_0[-1])
                exit_status = 1  # Stop checking things
                write_output('{} >> all'.format(pi_0[-1]), lengths, pi_RV, winner)
                break
            elif infinite_longer(lengths[alphabet.index(pi_0[-1])], lengths[alphabet.index(pi_0[x])]):
                # pi_0 >>> than the x'th interval (in alphabetic order)
                count += 1
            else:
                # pi_0 is not(>>>) than some interval.
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
                exit_status = 1

                write_output('{} >> all'.format(pi_1[-1]), lengths, pi_RV, winner)
                break
            elif infinite_longer(lengths[alphabet.index(pi_1[-1])], lengths[alphabet.index(pi_1[x])]):
                count += 1
            else:
                break
        if exit_status == 1:
            break


#TODO: we already calculated these two values, pull them from above.

        # Use this to hold truth value of whether current top >>> current bot
        top_inf_bot = infinite_longer(lengths[alphabet.index(pi_0[-1])], lengths[alphabet.index(pi_1[-1])])

        # Use this to hold truth value of whether bot >>> top
        bot_inf_top = infinite_longer(lengths[alphabet.index(pi_1[-1])], lengths[alphabet.index(pi_0[-1])])


# CHECK 3:

        ## if neither of these is true we don't yet know if we are in a repeating cycle that continues infinitely;
        ## even if CHECK 3 is satisfied, if neither is true, then that doesn't determine the future.

        ## If one of the two right-most intervals is >>> than the other, we check if there is a periodic
        ## cycle of similiar situations. The one >>> larger is also the next winner.

        #print 'Check if any of the (number of intervals -1) last iterations had the same permutation'
        # Since inifite-iterating cycles can be at most (num. intervals - 1) long
        # start that far back and move forward:

        if (top_inf_bot == True               ### SHOULD DEFINITELY CLEAN THIS UP BC
            or bot_inf_top == True):          ### COMPUTATIONALLY THINGS ARE REPEATED UNNCEESSARILY BELOW AND ABOVE

            #for i in reversed(list(range(1, min(num_intervals, num_iterations+1)))):
            i = min(num_intervals-1, num_iterations)
            while i > 0:
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


#TODO: Fix given following note:
# =============================================================================
#   For shorthand call num_intervals num_ints
#   Here we do comparisons for i = num_ints -1, num_ints - 2, ..., 1.
#   The comparisons are for the iteration (num_ints - i).
#   say the comparision only fails for iteration (num_ints - 1):
#     Here, we will run:
#       i = num_ints -1 --> (num_ints, num_ints -1, ..., 1 [FAILURE])
#       then  i = num_ints -2 -->    ( num_ints -3, ..., 1 [Failure])
#       then  i = num_ints -3 -->    ( num_ints -4, ..., 1 [failure])
#       ....
#       i = 1 [Failure]
#
#       Which at a worst case efficiency involves [(n^2 + n)/2 - n] = (n^2)/2 - n/2
# =============================================================================

## NOTE: this is  almost certainly not implimented efficently; (USE NUMPY, CLEAN UP CODE) currently this checked,
## and then if false we recalculate next_winner in the next iteration although it doens't change

                end_comparison = False

# We recheck these since we have new values post-induction:
                last_top = pi_0[-1]
                last_bot = pi_1[-1]
                top_idx = alphabet.index(last_top)
                bot_idx = alphabet.index(last_bot)
                longer_interval = lex_longer(lengths[top_idx], lengths[bot_idx])
                #print("i: ", i)
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
#   we can check to see if for all of the induction steps inbetween, the same interval
#   (top or bot) would win based on our current lengths, as the interval
#   that won before.
# AND if the winner in our current lengths is infinitely larger than the loser
#   (for all pairs of winner and loser in the cycle)
#   then we know that the sequence of permutations will allways repeat in same way
#   it has for these previous i permutations; and so we know the induction
#   continues forever in a fixed pattern.

                    if end_comparison == True:
                        break

                    if exit_status == 1:
                        break


# If the above is satisfied; check if it is also satisfied for the following iterations:

                    forward_it = 1  # how far forward from where i is to check
                    win_count = 0   # increments the number of times our current RV-setup wins

                    while forward_it <= i:   # We have checked i-many iterations back already
                        #print 'forward it ran'
                        # e,g, i = 4, forward_it = 1, 2, 3, (on 4: win_count=3)
                        #       ---> checking 4-1=3, 4-2=2, 4-3=1 iterations back
                        #       say forward it fails on 2, then i-forward_it = 2,
                        #       and there is no point checking:
                        #           i=3, forward_it=1 [fail]
                        #       -------- skip ahead to:
                        #           i=2, forward_it=1 (possibly passes)
                        #
                        #
                        #
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
                            if infinite_longer(lengths[prev_top_idx], lengths[prev_bot_idx]):
                                win_count += 1     # keeping track of how often this occurs
                                forward_it += 1    # increase forward_it by 1 to look another iteration more recent
                                cycle = cycle + '{}-{} '.format(previous_top, previous_bot)
                            else:
                                ## the winner was top, but can't be sure this pattern
                                ## repeats forever because in its current state the winner is not inf larger
                                end_comparison = True
                                i -= (forward_it)


                        elif infinite_longer(lengths[prev_bot_idx],lengths[prev_top_idx]):
                            # know winner is bot because winner == top was not true
                            # so we just look to see if the winner is inf longer
                            win_count += 1
                            forward_it += 1
                            cycle = cycle + '{}-{} '.format(previous_bot, previous_top)
                        else:
                            # the winner is bottom but in current lengths the
                            # winner would not be infinitely larger; so this i fails
                            end_comparison = True
                            i -= (forward_it)
                            break
                else:
                    i -= 1

        if exit_status == 1:
            break

    return
    # Pretty sure this stat is unreachable.
    #sys(exit)
#
# END OF CHECKING POST-INDCTION
# END OF ITERATION FOR EXAMPLE
# =============================================================================


# Setup that runs when program is run to set options:
print('')
print('')
#print('USER INPUTS:')
#print('')

def run_program(num_intervals=4, dimension=3, component_vals=[(1,5),(-5,5),(-5,5)],
                num_examples=10000, max_iterations=10000, filename_input=None,
                only_write_halts=False, write_lengths=True, print_running_info=True, write_nothing=False):

#TODO: Do not use global variables!!!
    global file_lengths
    global file_permutation
    global file_example_number
    global file_matrix_rank
    global write_all
    global halt_count
    global verbose
    global int_dim
    global subint
    global has_header
    global halt_has_header
    global print_only
    global do_not_write
    global iteration_count

    iteration_count = 0

     # A list containing time stamps used to generate runtimes
    do_not_write = write_nothing

    has_header = False                 # Does the output csv file alerady have a header row. Lets assume no
    halt_has_header = False            # Does the halting output csv file alerady have a header row. Lets assume no
    print_only = False                 # If True output is printed in console not written to file


    runtimes = []                      # A list to hold the runtime of each example
    timestamps =[]                     # A list containing time stamps used to generate runtimes

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
            overwrite_1 = input('Overwrite files in run_1: True / False ?')
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
        print('Component Value Bounds: ', c_vals)

        #if len(c_vals) < int_dimension:
        #    for h in int_dim - c_vals:
        #        c_vals.extend(c_vals[-2],c_vals[-1])
        example_start = time.time()
        examples, ex_perms = build_examples(num_ints, int_dim, c_vals, permutations, num_exs)
        if print_running_info:
          print('Took %f seconds' % (time.time() - example_start))

    global writer
    global halt_writer

    with open (run_dir + '/' + filename_halt, 'a+') as output_halt_file:
        halt_writer = csv.writer (output_halt_file, dialect='halt_dialect')

        with open(run_dir + '/' + filename_output, 'a+') as output_file:
            writer = csv.writer(output_file, dialect='dialect')


            if filename_input is not None: #This is for running specific examples
#TODO: Check this still works!
#TODO: This almost certainly doesn't work

                with open(filename, "r") as input_file:
                    reader = csv.DictReader(input_file, dialect='rv_program_dialect')

                    start = time.time()

                    for row in reader:
                        file_example_number = int(row['EXAMPLE_NUMBER'].strip())
                        file_num_intervals = int(row['NUMBER_INTERVALS'].strip())
                        file_interval_dimension = int(row['INTERVAL_DIMENSION'].strip())
                        file_permutation = row['PERMUTATION'].strip().upper()
                        lengths_temp = row['LENGTH_COMPONENTS'].strip().split()
                        file_lengths = []
                        for k in lengths_temp:
                            file_lengths.append(list(map(int,(k.split(',')))))

                        subint = ''                    #String containing the name of the subintervals

                        num_intervals = file_num_intervals
                        int_dim = file_interval_dimension

                        for i in range(num_intervals):
                            subint = subint + string.ascii_uppercase[i]

                        lengths = copy.deepcopy(file_lengths)

                        subint_2 = copy.copy(file_permutation)

                        # At every 50,000th example, note how long it has taken.
                        if (file_example_number % 50000 == 0) and (file_example_number > 1):
                            timestamps.append(time.time())
                            if len(timestamps) == 1:
                                runtimes.append(timestamps[0]-start)
                                print('Time at Example {:,}: '.format(file_example_number) + 'Took %.1f seconds' % (runtimes[0]))
                            else:
                                runtimes.append(timestamps[-1] - timestamps[-2])
                                print('Time at Example {:,}: '.format(file_example_number) + 'Took %.1f seconds ' % (runtimes[-1]) + '(%.1f minutes total)' % (sum(runtimes)/60))


            # ITERATE THE RV INDUCTION:

                        iterate(num_intervals, int_dimension, lengths, subint, subint_2, max_iterations)



            else:
                start = time.time()
                if print_running_info:
                  print('Running examples...')
                #print('This is (relatively) safe to stop at any time (the last file entry will likely be broken though)')
                file_example_number = 0

                for ex in range(len(examples)):
                    file_num_intervals = num_ints
                    file_interval_dimension = int_dim
                    file_permutation = ex_perms[i]
                    file_lengths = examples[i]


                    subint = ''                    #String containing the name of the subintervals
                    num_intervals = file_num_intervals
                    int_dim = file_interval_dimension

                    for i in range(num_intervals):
                        subint = subint + string.ascii_uppercase[i]

                    lengths = copy.deepcopy(file_lengths)

                    subint_2 = copy.copy(file_permutation)

                    #file_matrix_rank = np.linalg.matrix_rank(np.matrix(file_lengths))

                    # At every 250,000th example, note how long it has taken.
                    if (file_example_number % 250000 == 0) and (file_example_number > 1):
                        timestamps.append(time.time())
                        if len(timestamps) == 1:
                            runtimes.append(timestamps[0]-start)
                            if print_running_info:
                              print('Time at Example {:,}: '.format(file_example_number) + 'Took %.1f seconds' % (runtimes[0]))
                        else:
                            runtimes.append(timestamps[-1] - timestamps[-2])
                            if print_running_info:
                              print('Time at Example {:,}: '.format(file_example_number) + 'Took %.1f seconds ' % (runtimes[-1]) + '(%.1f minutes total)' % (sum(runtimes)/60))

        # ITERATE THE RV INDUCTION:
                    iterate(num_intervals, int_dimension, lengths, subint, subint_2, max_iterations)
                    file_example_number += 1

            # After iterating all examples, print how long functions took:
            if file_example_number < 1000001:
              print('Halting examples: {}/{};  {}%'.format(halt_count, file_example_number, (halt_count/file_example_number)*100))
            else:
              print('Halting examples: {:,}/{:,};  {}%'.format(halt_count, file_example_number, (halt_count/file_example_number)*100))
            end = time.time()
            print('Average iterations: {}'.format(iteration_count/file_example_number))
            print('Iterations per second: {}'.format(iteration_count/(end - start)))
            print('Examples per second: {}'.format(file_example_number/(end-start)))
            if print_running_info:
              print('Took %f seconds' % (end - start))
              print('================================\n\n')




######
# RUN PROGRAM:
#
for i in range(1,2):
    run_program(component_vals=[(1,i),(-1*i,i),(-1*i,i)], num_examples=500000, print_running_info=True, write_nothing=False)

#
#
#
######

"""
Number of possible examples for
m = number of itervals
d = interval dimension
n = numerical bound, where for an interval, say, A

len_lex(A) : [a_0, a_1, .., a_{d-1}]
and we are bounding 0 <  a_0 <= n
and                -n <= a_i <= n  for all i =/= 0

Then the number of possible lengths for A is:

  [a_0, a_1, .., a_{d-1}]
    n * (2n+1)^{d-1}

Since there are m intervals we have the number of possible lengths for all m:

  [n * (2n+1)^{d-1}]^m

  and then of course (roughly) ~ m! permutations of the intervals for
  (~m!)* [n * (2n+1)^{d-1}]^m

  m! = O(m^m)

Which is O(m^m * n^{dm})

if d, m fixed, and n varies,

we have ~ O(n^{dm})  = O({numerical bound}^{#dimensions*#intervals}).

I will note, for reasonable values of d=3, m=4,
# examples for n=1 ~ 78,000              7.5*10^4
# examples for n=2 ~ 75,000,000          7.5*10^7
# examples for n=3 ~ 5,600,000,000       5.6*10^9
# examples for n=4 ~ 132,239,526,912         10^11
# examples for n=5 ~                         10^12
# examples for n=6 ~                         10^13
# examples for n=10 ~                        10^15
# examples for n=100 ~                       10^27
# examples for n=1000 ~                      10^39




Since examples are sampled randomly, we expect O(k^{2}/(2*X)) repeated examples,
where k is number of examples computed, and X  is the number of possilbe examples

"""












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