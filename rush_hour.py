import os
import re
import sys
from z3 import *
import numpy as np
from itertools import combinations

redcar=[]
verticalcars=[]
horizontalcars=[]
mines=[]
n=0
limit=0

#print("hello")

input_line=1
with open(sys.argv[1],'r') as input_file:
    for line in input_file:
        data=line.split(",")
        if(input_line==1):
            n=int(data[0])
            limit=int(data[1])
            #print(n)
            #print(limit)
        elif(input_line==2):
            redcar.append(int(data[0]))
            redcar.append(int(data[1]))
        else:
            if(int(data[0])==0):
                verticalcars.append([ int(data[1]),int(data[2]) ])
            elif(int(data[0])==1):
                horizontalcars.append([ int(data[1]),int(data[2]) ])
            else:
                mines.append([ int(data[1]), int(data[2]) ])

        input_line=input_line+1


num_vert=len(verticalcars) 
num_hor=len(horizontalcars)

'''print(redcar)
print(verticalcars)
print(horizontalcars)
print(mines)
print(num_hor)
print(num_vert)'''

sat_solver=Solver()


mines_b=[ [ Bool ("mine_{}_{}".format(i,j)) for j in range(n)] for i in range(n)]

#print(mines_b)

for i in range(n):
    for j in range(n):
        if [i,j] in mines:
            sat_solver.add(mines_b[i][j])
        else:
            sat_solver.add(Not(mines_b[i][j]))

red_b=[ [ Bool ("red_{}_{}".format(i,j)) for j in range(limit+1)] for i in range(n-1)] 
#it stores boolean variables for all instances (j) with the column number of the redcar(i)

#print(red_b)

#sat_solver.add(red_b[n-2][limit])
'''emp=[]
for i in range(limit+1):
    emp.append(red_b[n-2][i])

sat_solver.add(Or(emp))'''


for i in range(n-1):
    if redcar[1]==i:
        sat_solver.add(red_b[i][0])
    else:
        sat_solver.add(Not(red_b[i][0]))

hor_b=[ [ [ Bool ("hor_{}_{}_{}".format(i,j,k)) for k in range(limit+1)] for j in range(n-1)] for i in range(num_hor) ]

for i in range(num_hor):
    for j in range(n-1):
        if horizontalcars[i][1]==j:
            sat_solver.add(hor_b[i][j][0])
        else:
            sat_solver.add(Not(hor_b[i][j][0]))


ver_b=[ [ [ Bool ("ver_{}_{}_{}".format(i,j,k)) for k in range(limit+1)] for j in range(n-1)] for i in range(num_vert) ]

#print(ver_b)

for i in range(num_vert):
    for j in range(n-1):
        if verticalcars[i][0]==j:
            sat_solver.add(ver_b[i][j][0])
        else:
            sat_solver.add(Not(ver_b[i][j][0]))

red_shift=[ [ Bool ("red_shift_{}_{}".format(i,j)) for j in range(limit)] for i in range(2)]    # check if limit is sufficient
#1-> forwards , 0-> backwards




        #sat_solver.add( Or( Not(ver_shift[j][0][i]), Not(ver_shift[j][1][i]) ) )
        #sat_solver.add( Or( Not(hor_shift[j][0][i]), Not(hor_shift[j][1][i]) ) )
    #sat_solver.add( Or(Not(red_shift[0][i]), Not(red_shift[1][i])) )

#print(red_shift)

hor_shift=[ [ [ Bool ("hor_shift_{}_{}_{}".format(i,j,k)) for k in range(limit)] for j in range(2)] for i in range(num_hor) ]
#0->back

#print(hor_shift)

#for i in range(limit):
    #for j in range(num_hor):
        #sat_solver.add( Or( Not(hor_shift[j][0][i]), Not(hor_shift[j][1][i]) ) )

ver_shift=[ [ [ Bool ("ver_shift_{}_{}_{}".format(i,j,k)) for k in range(limit)] for j in range(2)] for i in range(num_vert) ]
#0->up
#print(hor_shift)

'''for i in range(limit):
    for j in range(num_vert):
        sat_solver.add( Or( Not(ver_shift[j][0][i]), Not(ver_shift[j][1][i]) ) )'''




for i in range(limit):
    move_list=[]
    move_list.append(red_shift[0][i])
    move_list.append(red_shift[1][i])
    for j in range(num_hor):
        move_list.append(hor_shift[j][0][i])
        move_list.append(hor_shift[j][1][i])
    for j in range(num_vert):
        move_list.append(ver_shift[j][0][i])
        move_list.append(ver_shift[j][1][i])

    for pair in combinations(move_list,2):
        a,b=pair[0],pair[1]
        sat_solver.add( Or( Not(a), Not(b) ))  #no more than one move
        sat_solver.add( Or(move_list) )        #atleast one move


    


#only one of the red_b should be true
for j in range(limit+1):
    li=[]
    for i in range(n-1):
        li.append(red_b[i][j])

    for pair in combinations(li,2):
        a,b=pair[0],pair[1]
        sat_solver.add( Or( Not(a), Not(b) ))

#only one of hor_b should be true
for k in range(num_hor):
    for j in range(limit+1):
        li=[]
        for i in range(n-1):
            li.append(hor_b[k][i][j])

        for pair in combinations(li,2):
            a,b=pair[0],pair[1]
            sat_solver.add( Or( Not(a), Not(b) ))

#only one of ver_b should be true
for k in range(num_vert):
    for j in range(limit+1):
        li=[]
        for i in range(n-1):
            li.append(ver_b[k][i][j])

        for pair in combinations(li,2):
            a,b=pair[0],pair[1]
            sat_solver.add( Or( Not(a), Not(b) ))

#keeping co-ord same when there is no movement (for redcar)

for j in range(limit):
    for k in range(n-1):
        sat_solver.add(Implies( Not(Or(red_shift[0][j],red_shift[1][j])) , Implies(red_b[k][j],red_b[k][j+1]) ) )


# for horcar

for p in range(num_hor):
    for j in range(limit):
        for k in range(n-1):
            sat_solver.add(Implies( Not(Or(hor_shift[p][0][j],hor_shift[p][1][j])) , Implies(hor_b[p][k][j],hor_b[p][k][j+1]) ) )

# for vercar

for p in range(num_vert):
    for j in range(limit):
        for k in range(n-1):
            sat_solver.add(Implies( Not(Or(ver_shift[p][0][j],ver_shift[p][1][j])) , Implies(ver_b[p][k][j],ver_b[p][k][j+1]) ) )




#changing co-ordinates for redcar (if movement)


for j in range(limit):
    for i in range(2):
        for k in range(n-1):
            if i==0 and k==0:
                sat_solver.add(Implies(red_b[k][j],Not(red_shift[i][j])))
            elif i==0 and k>0:
                sat_solver.add(Implies(red_shift[i][j], Implies(red_b[k][j],red_b[k-1][j+1]) ) )
            elif i==1 and k==n-2:
                sat_solver.add(Implies(red_b[k][j],Not(red_shift[i][j])))
            elif i==1 and k<n-2:
                sat_solver.add(Implies(red_shift[i][j], Implies(red_b[k][j],red_b[k+1][j+1]) ) )


#changing co-ordinates of hor_car
for p in range(num_hor):
    for j in range(limit):
        for i in range(2):
            for k in range(n-1):
                if i==0 and k==0:
                    sat_solver.add(Implies(hor_b[p][k][j],Not(hor_shift[p][i][j])))
                elif i==0 and k>0:
                    sat_solver.add(Implies(hor_shift[p][i][j], Implies(hor_b[p][k][j],hor_b[p][k-1][j+1]) ) )
                elif i==1 and k==n-2:
                    sat_solver.add(Implies(hor_b[p][k][j],Not(hor_shift[p][i][j])))
                elif i==1 and k<n-2:
                    sat_solver.add(Implies(hor_shift[p][i][j], Implies(hor_b[p][k][j],hor_b[p][k+1][j+1]) ) )

#changing co-ordinates of ver_car
for p in range(num_vert):
    for j in range(limit):
        for i in range(2):
            for k in range(n-1):
                if i==0 and k==0:
                    sat_solver.add(Implies(ver_b[p][k][j],Not(ver_shift[p][i][j])))
                elif i==0 and k>0:
                    sat_solver.add(Implies(ver_shift[p][i][j], Implies(ver_b[p][k][j],ver_b[p][k-1][j+1]) ) )
                elif i==1 and k==n-2:
                    sat_solver.add(Implies(ver_b[p][k][j],Not(ver_shift[p][i][j])))
                elif i==1 and k<n-2:
                    sat_solver.add(Implies(ver_shift[p][i][j], Implies(ver_b[p][k][j],ver_b[p][k+1][j+1]) ) )


'''emp=[]
for i in range(limit+1):
    emp.append(red_b[n-2][i])

sat_solver.add(Or(emp))'''

emp=[]
for i in range(limit):
    emp.append(red_b[n-2][i])

sat_solver.add((Or(emp)))
sat_solver.add(red_b[n-2][limit])
                
            
'''def empty(x,y,t):
    if [x,y] in mines:
        return False
    else:
        if x==redcar[0] and red_b[y][t]:
            return False
        else:
            for i in range(num_hor):
                if x==horizontalcars[i][0] and hor_b[i][y][t]:
                    return False
            for j in range(num_vert):
                if y==verticalcars[j][1] and ver_b[j][x][t]:
                    return False
    return True'''

def empty(x,y,t):
    arr=[]
    if(x<n and y<n and x>=0 and y>=0):
        arr.append(Not(mines_b[x][y]))
    if(x==redcar[0]):
        if(y<n-1 and y>=0 ):
            arr.append(Not(red_b[y][t]))
        if(y>0 and y<=n-1):
            arr.append(Not(red_b[y-1][t]))
    for i in range(num_hor):
        if(x==horizontalcars[i][0]):
            if(y<n-1 and y>=0):
                arr.append(Not(hor_b[i][y][t]))
            if(y>0 and y<=n-1):
                arr.append(Not(hor_b[i][y-1][t]))
    for j in range(num_vert):
        if(y==verticalcars[j][1]):
            if(x<n-1 and x>=0):
                arr.append(Not(ver_b[j][x][t])) 
                #print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
            if(x>0 and x<=n-1):
                arr.append(Not(ver_b[j][x-1][t]))
                #print("......................................................................") 
    #print(arr)
    return arr

for k in range(limit):      #check
    for j in range(n-1):
        sat_solver.add( Implies ( red_b[j][k], Implies( red_shift[0][k], And(empty(redcar[0],j-1,k))  )   ) )
        sat_solver.add( Implies ( red_b[j][k], Implies( red_shift[1][k], And(empty(redcar[0],j+2,k))  )   ) )
        '''if red_b[j][k]:
            if i==0:          #check for j==0
                sat_solver.add(Implies( red_shift[i][k], empty(redcar[0],j-1,k)  ) )
            elif i==1:
                sat_solver.add(Implies( red_shift[i][k], empty(redcar[0],j+2,k)  ) )'''

for p in range(num_hor):
    for k in range(limit):      #check
        for j in range(n-1):
            sat_solver.add( Implies ( hor_b[p][j][k], Implies( hor_shift[p][0][k], And(empty(horizontalcars[p][0],j-1,k) )) )   )
            sat_solver.add( Implies ( hor_b[p][j][k], Implies( hor_shift[p][1][k], And(empty(horizontalcars[p][0],j+2,k) )) )   )
            '''if hor_b[p][j][k]:
                if i==0:          #check for j==0
                    sat_solver.add(Implies( hor_shift[p][i][k], empty(horizontalcars[p][0],j-1,k)  ) )
                elif i==1:
                    sat_solver.add(Implies( hor_shift[p][i][k], empty(horizontalcars[p][0],j+2,k)  ) )'''


for p in range(num_vert):
    for k in range(limit):      #check
        for j in range(n-1):
            sat_solver.add( Implies ( ver_b[p][j][k], Implies( ver_shift[p][0][k], And(empty(j-1,verticalcars[p][1],k) )) )   )
            sat_solver.add( Implies ( ver_b[p][j][k], Implies( ver_shift[p][1][k], And(empty(j+2,verticalcars[p][1],k)) ) )   )
            '''if ver_b[p][j][k]:
                if i==0:          #check for j==0
                    sat_solver.add(Implies( ver_shift[p][i][k], empty(verticalcars[p][0],j-1,k)  ) )
                elif i==1:
                    sat_solver.add(Implies( ver_shift[p][i][k], empty(verticalcars[p][0],j+2,k)  ) )'''





#print(sat_solver.check())
if(sat_solver.check()==sat):
    temp=[]
    red_pos=[]
    hor_pos=[]
    ver_pos=[]
    m=sat_solver.model()
    for val in m:
        k=str(val)
        if is_true(m[val]) and "shift" in k:
            temp.append(k.split("_"))
        if is_true(m[val]) and "red" in k and not "shift" in k:
            red_pos.append(k.split("_"))
        if is_true(m[val]) and "hor" in k and not "shift" in k:
            hor_pos.append(k.split("_"))
        if is_true(m[val]) and "ver" in k and not "shift" in k:
            ver_pos.append(k.split("_"))
        
    '''print(temp)
    print(red_pos)
    print(hor_pos)
    print(ver_pos)'''
    for elem in temp:
        if elem[0]=="red":
            r=int(elem[3]) #instance
            if(int(elem[2])==0):
                print(redcar[0],int(red_pos[r][1]),sep=',')
            else:
                print(redcar[0],int(red_pos[r][1])+1,sep=',')
            #print(redcar[0])
        elif elem[0]=="hor":
            c=int(elem[2])  #car number
            h=int(elem[4])  #instance
            if(int(elem[3])==0):
                for q in hor_pos:
                    if c==int(q[1]) and h==int(q[3]):
                        print(horizontalcars[c][0],int(q[2]),sep=',')
            else:
                for q in hor_pos:
                    if c==int(q[1]) and h==int(q[3]):
                        print(horizontalcars[c][0],int(q[2])+1,sep=',')

        elif elem[0]=="ver":
            c=int(elem[2])  #car number
            h=int(elem[4])  #instance
            if(int(elem[3])==0):
                for q in ver_pos:
                    if c==int(q[1]) and h==int(q[3]):
                        print(int(q[2]),verticalcars[c][1],sep=',')
            else:
                for q in ver_pos:
                    if c==int(q[1]) and h==int(q[3]):
                        print(int(q[2])+1,verticalcars[c][1],sep=',')
            #print(redcar[0])
else:
    print("unsat")            



# atleast one move
# atmost one move
# is_empty()
# redcar reaches end