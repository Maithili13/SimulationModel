#===============================================================================
#= Program to calculate no wait resource need for Multi-Tier Intenvention      =
#===============================================================================
#= Notes:                                                                      =
#=  1) Need Python 3.6 or later installed                                      =
#===============================================================================
#= Execute: Command line as python Model_April_3_1.py Can take input file.     =
#===============================================================================
#= Sample execution: (as python Model_April_3_1.py < inputFileForModel.txt)    =
#=                                                                             =
#=   =======================================================================   =
#=   ==   Results from queueing model for Multi-Tier Intervention         ==   =
#=   =======================================================================   =
#=   == System parameters:                                                     =
#=   ==   Number of classrooms                   = 50                          =
#=   ==   Total number of at risk students       = 303                         =
#=   ==   Distribution of at risk students       = RAND                        =
#=   ==   Number of students per teacher or aide = 5                           =
#=   ==   Number of aides available              = 20                          =
#=   ==   Number of psychologists available      = 1                           =
#=   ==   Number of interventionists available   = 3                           =
#=   ==   1 (turn on) / 0 (turn off) verbose mode= 0                           =
#=   ==   Probability of response                = 0.7                         =
#=   ==   Number of students per psychologist    = 20                          =
#=   ==   Number of students per interventionist = 12                          =
#=   =======================================================================   =
#=   == Simulation Summary                                                     =
#=   ==   Total time to completion for all       =  37.0 weeks                 =
#=   ==   Mean waiting time for T2Lite           =  0.6  weeks                 =
#=   ==   Mean waiting time for Evaluation       =  1.6  weeks                 =
#=   ==   Mean waiting time for Intervention     =  6.3  weeks                 =
#=   ==   Time to complete T2Lite (50% students) =  6.0  weeks                 =
#=   ==   Time to complete T2Lite (75% students) =  6.0  weeks                 =
#=   ==   Time to complete Eval.  (50% students) =  9.0  weeks                 =
#=   ==   Time to complete Eval.  (75% students) =  10.0 weeks                 =
#=   ==   Time to complete Inter. (50% groups)   =  27.0 weeks                 =
#=   ==   Time to complete Inter. (75% groups)   =  27.0 weeks                 =
#=   ==   Mean waiting time for T2Lite           =  0.5  weeks                 =
#=   ==   Mean waiting time for Evaluation       =  1.3  weeks                 =
#=   ==   Mean waiting time for Intervention     =  6.3  weeks                 =
#=   ==   Student queue length for T2Lite        =  27                         =
#=   ==   Student queue length for Evaluation   =  56                          =
#=   ==   Group queue length Intervention        =  8                          =
#=   ==   Students moving to Tier 3 Intervention =  26                         =
#===============================================================================
#= For input file:                                                             =
#=                                                                             =
#=   50       #1    -> Number of classrooms                                    =
#=   303      #2    -> Total number of at risk students                        =
#=   RAND     #3    -> RAND for random distribution, UNIF for uniform distr.   =
#=   0        #4    -> Enter 1 (turn on) or 0 (turn off) for timeline          =
#=   20       #5    -> T2 Lite: Number of aides available presently            =
#=   1        #6    -> Evaluation: Number of psychologists presently           =
#=   3        #7    -> T2 Heavy: Number of interventionists presently          =
#=   5        #8    -> T2 Lite: Number of students per teacher or aide         =
#=   0.70     #9    -> T2 Lite: Probability response to T2 Lite                =
#=   0.70     #10   -> T2 Heavy: Probability response to T2 Heavy              =
#=   20       #11   -> Evaluation: Number of students per psychologist         =
#=   12       #12   -> T2 Heavy: Number of students per interventionist        =
#=                                                                             =
#===============================================================================
#= Author: Maithili Mishra (3/24/20)                                           =
#===============================================================================
#= History: Maithili (3/18/20) - Genesis                                       =
#=          KJC (03/23/20) - Updates for input from file                       =
#===============================================================================
import salabim as sim
import random
import math
import operator
from random import sample
from collections import OrderedDict

numAtRiskStudents = 0            # Number of at-risk students in all classrooms
numAides = 0                     # Number of teacher's aides available presently
numStuPerTeacherOrAide = 5       # Number of students handled per teacher/aide
numStuPerInterventionist = 12    # Number of students handled per interventionist
numStuPerPsychologist = 20       # Number of students handled per psychologist
numClassRooms = 0                # Number of classrooms
serviceTimeInClass = 6           # Time taken for one T2Lite cycle
serviceTimeIntervention = 10     # Time taken for one Intervention cycle
serviceTimeEvaluation = 0.05     # Time taken for one Evaluation cycle
numInterventionists = 3          # Number of interventionists
numPsychologists = 1             # Number of school psychologists
n = 0                            # Number of teachers and aides per classroom 
classIndex = 0                   # Number of teachers and aides per classroom 
counterTandA = 0                 # Counter to track treated students in T2Lite
counterEval = 0                  # Counter for treated students in Evaluation
counterInter = 0                 # Counter for treated students in Intervention
atrisk = []                      # Classwise number of atrisk students 
tempAtrisk = []                  # Temp arr of classwise number of atrisk stdnts 
aide = []                        # Number of aides per class
groupSize = 6                    # Intervention batch size (6)  
class_stats = []                 # Array for class wait 
evalWaittime = []                # Array for Evaluation wait time
interWaitTime = []               # Array for Intervention wait time
evaluatedLength = []             # Array for  Evaluation wait list length
verboseMode = 0                  # 1 (turn on) or 0 (turn off) for verbose mode
probResponse = 0.70              # T2 Lite: Probability of responding
probResponseT2Heavy = 0.70       # T2 Heavy: Probability of responding
distType = "UNIF"                # Distribution type
evaluatedTotal = -1              # Total students evaluated
counterEval50 = 0                # 50 % students complete Eval. Counter
counterEval75 = 0                # 75 % students complete Eval. Counter
occupancyT2Lite = []             # occupancy arr. for T2Lite
occupancyT2LiteRounded = []      # occupancy arr. for T2Lite
totalAtrisk = []                 # Arr. for at-risk students in all classrooms
see_evaluator = []               # students' probability of seeing an evaluator
evalNeeded= []                   # Arr. to tell if Eval needed for each student
evalCounterEnvData = dict()      # students complete Eval. Counter
T2LiteCounterEnvData = OrderedDict() # students complete T2Lite Counter
counterEvalList =[]              # Arr. for evaluation counters
evalEnvNow = []                  # Arr. for evaluation env.now()
counterInterList = []            # Arr. for Intervention counters
interEnvNow = []                 # Arr. for Intervention env.now()
counterT2LiteList = []           # Arr. for T2Lite counters
T2LiteEnvNow = []                # Arr. for T2Lite env.now()
timeToFinishT2Lite50 = 0         # time for 50 % students to complete T2Lite
timeToFinishT2Lite75 = 0         # time for 75 % students to complete T2Lite
timeToFinishT2Lite100 = 0        # time for 100 % students to complete T2Lite
StudentsRespondT2Lite = 0        # Number of students respond after T2 Lite 
timeToFinishEval100 = 0          # time for 100 % students to complete Eval
timeToFinishInter100 = 0         # time for 100 % students to complete Inter
counterEval100 = 0               # 100 % students complete Evaluation Counter
counterInter100 = 0              # 100 % students complete Intervention Counter
randSeed = 123                   # Random number seed
groups = numStuPerInterventionist / 6 # T2Heavy groups
print("   \n\n   *** Queueing Model of a Multi-Tiered System of Support ***\n")

#==============================================================================
#    Simulation inputs from the user                                                            
#==============================================================================
print("SIMULATION INPUTS...")

# Input system parameters
#inString = input("Enter 1 (turn on) or 0 (turn off) for verbose mode: ")
#verboseMode  = int(inString.split()[0])
inString = input("Number of classrooms: ")
numClassRooms = int(inString.split()[0])
inString = input("Total number of at risk students: ")
numAtRiskStudents = int(inString.split()[0])
#inString = input("Enter UNIF for uniform, RAND for random: ")
#distType = inString.split()[0]
#inString = input("Enter random number seed for random distribution: ")
#randSeed = inString.split()[0]
inString = input("T2 Lite: Number of aides: ")
numAidesAvailable = int(inString.split()[0])
#inString = input("T2 Lite: Number of students per teacher or aide: ")
#numStuPerTeacherOrAide = int(inString.split()[0])
#inString = input("T2 Lite: Probability of responding: ")
#probResponse = float(inString.split()[0])
inString = input("Evaluation: Number of psychologists available: ")
numPsychologists = int(inString.split()[0])
#inString = input("Evaluation: Number of students per psychologist per week: ")
#numStuPerPsychologist = int(inString.split()[0])
inString = input("T2 Heavy: Number of interventionists: ")
numInterventionists  = int(inString.split()[0])
#inString = input("T2 Heavy: Number of students per interventionist: ")
#numStuPerInterventionist = int(inString.split()[0])
#inString = input("T2 Heavy: Probability respond to T2 Heavy: ")
#probResponseT2Heavy = float(inString.split()[0])
psychCapacity = numPsychologists * 20 # students handled in Evaluation per week
interCapacity = numInterventionists # groups handled in Intervention  

#==============================================================================
#    Aide allocation according to the number of atrisk students in class.
#    Aides are allocated according to the requirement. 
#    If there are 15 students in class, then 2 aides are allocated
#    If there are lesser number of aides than required, 
#    the remaining number of aides are allocated to the class
#==============================================================================


for i in range(numAtRiskStudents):
    atrisk.append(0)             # create an array for atrisk population 

# Distribute at risk students to classrooms

for i in range(numAtRiskStudents):
    if (distType == "UNIF" or distType == "unif"):
        classIndex = i % numClassRooms
    else:  
        # randomly distribute atrisk students        
        classIndex = sim.random.randint(0, (numClassRooms - 1))
    atrisk[classIndex] += 1     # atrisk student assignment to classes 

#if verboseMode == 1:
    #print("======================================================================")
    #print("Classwise presence of at-risk students")
    #print("======================================================================")
    
#if verboseMode == 1:
    #for i in range(numClassRooms):
        #print("Class", i + 1, " = ", atrisk[i])


#==============================================================================
for i in range(numClassRooms):
    aide.append(0)

tempAtrisk = atrisk.copy()


# Determine the number of aides per class in array aide[]
numAides = numAidesAvailable
for i in range(numClassRooms):
    # allocate an aide when the student number reaches a multiple of 5
    if (tempAtrisk[i] > numStuPerTeacherOrAide ) & (numAides > 0):
        if (tempAtrisk[i] / numStuPerTeacherOrAide ).is_integer():
            numbaides = (tempAtrisk[i] / numStuPerTeacherOrAide ) - 1
        else: 
            numbaides = math.floor(tempAtrisk[i] / numStuPerTeacherOrAide ) 
        if (numbaides < numAides):
            aide[i] += numbaides
        else:
            aide[i] = numAides
        
        numAides -= numbaides
        if numAides <= 0:
            break

#============================================================================== 

UnevalLength = int(round(float((1 - probResponse) * (numAtRiskStudents)), 0))

for i in range(numAtRiskStudents):
    totalAtrisk.append(i)

for i in range(numAtRiskStudents):
    see_evaluator.append(0)

for i in range(numAtRiskStudents):
    see_evaluator = random.sample(totalAtrisk, UnevalLength)
    
for i in range(numAtRiskStudents):
    evalNeeded.append(0)

for identifiedStudent in see_evaluator:
    evalNeeded[identifiedStudent] = 1


#============================================================================== 

class Student(sim.Component):
    def setup(self, classroom):
        self.classroom = classroom

    def process(self):
        self.enter(T2LiteIncomplete)
        # Teacher/Aide requested
        yield self.request(
        (self.classroom.n_staff)) 
        if (env.now() % 6 == 0):
            # Sessions over a period of 6 weeks
            yield self.hold(serviceTimeInClass)
            # Counter to track completed students in T2Lite
            global counterTandA
            # Counter incremented after a 6 week session
            counterTandA += 1
          
            counterT2LiteList.append(counterTandA)
            T2LiteEnvNow.append(float(math.ceil(env.now())))                
            #print(self.classroom.n_staff._claimers.departure_rate())
            if verboseMode == 1:
            # Print the completion status
                print("Week", float(math.ceil(env.now())), ": student", 
                      counterTandA, "completes T2Lite")             
            # Array for wait times of T2Lite
            if (env.now() <= 6):
                class_stats.append(int(self.classroom.n_staff.requesters().length_of_stay.minimum()))
            if (env.now() > 6):
                class_stats.append(int(self.classroom.n_staff.requesters().length_of_stay.maximum()))
         
                
        evalCheck = evalNeeded[-1]
        evalNeeded.pop()
        # 30% of students see the psychologist 
        if evalCheck == 1:
            
            self.enter(unevaluated)
            eval_weeks = int(math.ceil((unevaluated.length() / psychCapacity)))
            global counterEval
            # psychologist requested
            yield self.request(psychologist)
            # Counter incremented after a 0.05 week session
            yield self.hold(serviceTimeEvaluation) 
            # array for wait times of students entering Evaluation
            evalWaittime.append(int(float(math.ceil(env.now())) + eval_weeks - 1 - self.enter_time(unevaluated) - 1))
            counterEval += 1
            counterEvalList. append(counterEval)
            evalEnvNow.append(float(math.ceil(env.now())) + eval_weeks - 1)
            if verboseMode == 1:
                # Print the completion status 
                print("Week", float(math.ceil(env.now())) + eval_weeks - 1 ,  ": student", 
                      counterEval, "completes Evaluation")    
            #enter evaluated queue
            self.enter(evaluated)
            #leave unevaluated queue
            self.leave(unevaluated)
           
     
            #Check if a batch of 6 is now formed
            if (counterEval % groupSize) == 0:   
                
                #Interventionist requested
                yield self.request((interventionist, (1/groups)))
                # Sessions conducted over a 10 weeks duration
                yield self.hold(serviceTimeIntervention)
                # Counter for treated students in Intervention
                global counterInter
                # Counter incremented after a sessions over a 10 week time frame 
                counterInter += 1
                counterInterList. append(counterInter)
                interEnvNow.append(float(math.ceil(env.now())))
                if verboseMode == 1:
                    # Print the completion status 
                    print("Week", float(math.ceil(env.now())), ": Group", 
                          counterInter, "completes Intervention")
                self.enter(interventionComplete)
                                
                # array for wait times of students entering Intervention
                interWaitTime.append(math.floor((float(math.ceil(env.now()))) - self.enter_time(evaluated) - 10))
                yield self.release()
               
            
#==============================================================================                
# setup a classroom with atrisk students and resources
class Classroom(sim.Component):
    def setup(self, at_risk_count, n_staff):
        self.at_risk_count = at_risk_count
        self.n_staff = sim.Resource(self._name+'.staff', capacity = n_staff)
                                       
        
    def process(self):
        # process each student 
        for _ in range(self.at_risk_count):
            Student(classroom=self)
            
          

#==============================================================================
def make_classrooms(numClassRooms, numAtRiskStudents, numAides):

    classrooms = {}

    for i in range(numClassRooms):
        classrooms[str(i)] = {'at_risk_count': 0,
                              'n_staff': 0}    
  
    for i in range(numClassRooms):
        # Initialize the resource (teachers and aides) per class with determined capacity
        classrooms[str(i)]['n_staff'] = numStuPerTeacherOrAide * (aide[i] + 1)
         # Initialize the atrisk count for each class
        classrooms[str(i)]['at_risk_count'] = atrisk[i]
   
    return classrooms

classrooms = make_classrooms(numClassRooms, numAtRiskStudents, numAides)

# Setup the simulation environment   
env = sim.Environment(trace=False, time_unit='weeks')

# Initialize the resource (psychologists) with known (user input) capacity
psychologist = sim.Resource("psychologists", capacity=psychCapacity)
# Initialize the resource (interventionists) with known (user input) capacity
interventionist = sim.Resource("interventionist", capacity=interCapacity)
 
# queues to track Phases
T2LiteIncomplete = sim.Queue('T2LiteIncomplete')
T2LiteComplete = sim.Queue('T2LiteComplete')
unevaluated = sim.Queue('unevaluated')
evaluated = sim.Queue('evaluated')
interventionComplete = sim.Queue('interventionComplete')



if verboseMode == 1:
    print("\n")
    print("======================================================================")
    print("Timeline for possible phase completions for the students              ")
    print("======================================================================")   

for classroom, details in classrooms.items():
    Classroom(classroom, **details)
    
    
#==============================================================================
#            Run the simulation    
#==============================================================================            

env.run()

print("\n")

#==============================================================================            
# Time to finish X percentage students calculations
#==============================================================================            

#T2Lite
T2LiteCounterEnvData = {counterT2LiteList[i]: T2LiteEnvNow[i] for i in range(len(counterT2LiteList))} 
counterT2Lite50 = int(round(float((numAtRiskStudents * 0.5)), 0))
counterT2Lite75 = int(round(float((numAtRiskStudents * 0.75)), 0))
timeToFinishT2Lite50 = T2LiteCounterEnvData.get(counterT2Lite50)
timeToFinishT2Lite75 = T2LiteCounterEnvData.get(counterT2Lite75)
timeToFinishT2Lite100 = sorted(T2LiteCounterEnvData.values())[-1]
StudentsRespondT2Lite = numAtRiskStudents - evaluated.length()

#Evaluation
evaluatedTotal = evaluated.length()
evalCounterEnvData = {counterEvalList[i]: evalEnvNow[i] for i in range(len(counterEvalList))} 
counterEval50 = int(round(float((evaluatedTotal * 0.5)), 0))
counterEval75 = int(round(float((evaluatedTotal * 0.75)), 0))
timeToFinishEval50 = evalCounterEnvData.get(counterEval50)
timeToFinishEval75 = evalCounterEnvData.get(counterEval75)
timeToFinishEval100 = evalCounterEnvData.get(evaluatedTotal)

#Intervention
global InterTotal 
InterTotal = interventionComplete.length()
InterCounterEnvData = {counterInterList[i]: interEnvNow[i] for i in range(len(counterInterList))} 
counterInter50 = int(round(float((InterTotal * 0.5)), 0))
counterInter75 = int(round(float((InterTotal * 0.75)), 0))
timeToFinishInter50 = InterCounterEnvData.get(counterInter50)
timeToFinishInter75 = InterCounterEnvData.get(counterInter75)
timeToFinishInter100 = InterCounterEnvData.get(InterTotal)

#==============================================================================
#Simulation  Summary                                                        
#============================================================================== 
# Computations for total time, average waiting times, queue lengths
AvgWaitTimeT2Lite = round(float(sum(class_stats) / len(class_stats)), 1)
AvgQueueLenT2Lite = round(float(len(class_stats) - class_stats.count(0)), 1)
AvgCompTimeT2Lite = AvgWaitTimeT2Lite + serviceTimeInClass
AvgWaitTimeEval = round(float(sum(evalWaittime) / len(evalWaittime)), 1)
AvgQueueLenEval = round(float(len(evalWaittime) - evalWaittime.count(0)), 1)
AvgCompTimeEval = AvgWaitTimeEval + math.ceil(serviceTimeEvaluation)
if len(interWaitTime):
    AvgWaitTimeInter = round(float(sum(interWaitTime) / len(interWaitTime)), 1)
    AvgQueueLengthInter = round(float(len(interWaitTime) - interWaitTime.count(0)), 1)  
    AvgCompTimeInter = AvgWaitTimeInter + serviceTimeIntervention
StuMovingToT3 = int(round(float((evaluatedTotal * (1 - probResponseT2Heavy))), 0))
StuRespondInter = int(round(float((evaluatedTotal * (probResponseT2Heavy))), 0))
GroupT2Heavy = int(round(float((evaluatedTotal / 6)), 0))
timelineOutput = "DISABLED"
if verboseMode == 1:
    timelineOutput = "ENABLED"
else:
    timelineOutput = "DISABLED"

#==============================================================================   



print("=======================================================================")
print("==   Results from queueing model for Multi-Tier Intervention         ==")
print("=======================================================================")
print("== Simulation parameters:")
print("== Timeline Output                                     =", timelineOutput)
print("== Random number seed for random distribution          =", randSeed)
print("=======================================================================")
print("== System parameters:")
print("==   Number of classrooms                              =", numClassRooms)
print("==   Total number of at risk students                  =", numAtRiskStudents)
print("==   Distribution of at risk students                  =", distType)
print("==   T2 Lite: Number of aides                          =", numAidesAvailable)
print("==   T2 Lite: Number of students per teacher or aide   =", numStuPerTeacherOrAide)
print("==   T2 Lite: Probability respond to T2Lite            =", probResponse)
print("==   Evaluation: Number of psychologists               =", numPsychologists)
print("==   Evaluation: Number of students per psych per wk   =", numStuPerPsychologist)
print("==   T2 Heavy: Number of interventionists              =", numInterventionists)
print("==   T2 Heavy: Number of students per interventionist  =", numStuPerInterventionist)
print("==   T2 Heavy: Probability respond to T2Heavy          =", probResponseT2Heavy)
print("=======================================================================")
print("== Simulation Summary ");
print("=======================================================================")
print("==   Number of students entering T2 Lite               = ",  numAtRiskStudents)
print("==   Time to complete 50% of students thru T2 Lite     = ", timeToFinishT2Lite50,
       " weeks")
print("==   Time to complete 75% of students thru T2 Lite     = ", timeToFinishT2Lite75,
       " weeks")
print("==   Time to complete all of students thru T2 Lite     = ", 
       timeToFinishT2Lite100, " weeks")
print("==   Mean waiting time for T2Lite                      = ", 
      AvgWaitTimeT2Lite, " weeks")
print("==   Mean completion time for T2Lite                   = ", 
      AvgCompTimeT2Lite, " weeks")
print("==   Mean number of students waiting for T2 Lite       = ", int(AvgQueueLenT2Lite))
print("==   Number of students respond after T2 Lite          = ", StudentsRespondT2Lite)
print("==   Number of students not respond after T2 Lite      = ", evaluatedTotal)
print("==------------------------------------------------------------------------")
print("==   Number of students entering Evaluation            = ", evaluatedTotal)
print("==   Time to complete 50% of students thru Evaluation  = ", timeToFinishEval50,
        " weeks")
print("==   Time to complete 75% of students thru Evaluation  = ", timeToFinishEval75,
        " weeks")
print("==   Time to complete all of students thru Evaluation  = ", timeToFinishEval100,
        " weeks")
print("==   Mean waiting time for Evaluation                  = ", AvgWaitTimeEval,
        " weeks")
print("==   Mean completion time for Evaluation               = ", AvgCompTimeEval,
        " weeks")
print("==   Mean number of students waiting for Evaluation    = ", int(AvgQueueLenEval))
print("==------------------------------------------------------------------------")
print( "==   Number of groups entering T2 Heavy                = ", GroupT2Heavy)
print( "==   Number of students entering T2 Heavy              = ", evaluatedTotal)
print( "==   Time to complete 50% of students thru T2 Heavy    = ", timeToFinishInter50,
        " weeks")   
print( "==   Time to complete 75% of students thru T2 Heavy    = ",
       timeToFinishInter75, " weeks")    
print( "==   Time to complete all of students thru T2 Heavy    = ", 
       timeToFinishInter100, " weeks") 
if len(interWaitTime):
    print("==   Mean waiting time for T2 Heavy                    = ", 
          AvgWaitTimeInter, " weeks")
if len(interWaitTime):
    print("==   Mean completion time for T2 Heavy                 = ", 
          AvgCompTimeInter, " weeks")    
if len(interWaitTime):
    print("==   Mean number of groups waiting for T2 Heavy        = ", 
          int(AvgQueueLengthInter))
print("==   Number of students respond after T2 Heavy         = ", StuRespondInter)          
print("==   Students moving to Tier 3 Intervention            = ", StuMovingToT3)    
print("=======================================================================")


