from openai import OpenAI
import subprocess
import json
import re
import pdb
import os
import time
import sys 
#from subprocess import call

lfunc = ["f_dummylist", "f_dummylistc", "f_dummyTree"]



def writeToBenchmarkFile(cprog, compcertast, vstspec, flist, filename): 
  #open the file to write
  fb = open("proverLLMSpec/"+filename, "w")
  fb.write("Given the C-code, corresponding compcert AST and VST specification below,\n")
  fb.write("C-code:\n")
  fb.write(cprog)
  fb.write("\n\n")
  fb.write("Compcert AST:\n")
  fb.write(compcertast)
  fb.write("\n\nVST specification:\n")
  fb.write(vstspec)
  if len(flist) > 0:
    fb.write("\n\nHere are the specifications of the other functions in the same file. Some of the functions below are called by the C-code above: \n")
  #all the specifications
  for fl in flist:
    fb.write(fl)
    fb.write("\n\n")
  fb.write("\n\nYour task is to prove the goals of the lemma below by specifying a set of tactics to advance the current goal. \n")
  fb.write("The interpreted state would then be returned back to you and you will predict the next set of tactics, till a fixpoint is reached, or the proof is completed. All tactics you predict, must be only relevant to the current goal. \n")
  fb.close()
#functions permitted to use
def matches_patternDeclare(s):
    pattern = r"^DECLARE .+$"
    return re.match(pattern, s) is not None

#functions being used
def matches_patternDefinition(s):
    pattern = r"^Definition .+ := \{\|$"
    return re.match(pattern, s) is not None


#check bias
def checkLoopsOrfName(filename):
   with open(filename, "r") as file:
    for line in file:
        # Process each line
        vline = line.strip()
        res = matches_patternDefinition(vline)
        if res == True:
            fname = vline.split(" ")[1]
            #jelper detect
            if not (fname in lfunc):
                return False
        if "Sloop" in vline:
            return False
   return True
            

#check whether the helper function is in the line
def checkMemberHelper(gl, vline): 
  for h in gl: 
    if h in vline:
      return True
  return False

#helper specs
def returnHelperSpecs(gl, filename):
   retHelper = []
   spec = ''
   check = False
   with open(filename, "r") as file:
    for line in file:
        # Process each line
        vline = line
        if vline == "\n" and check == True:
          check = False 
          retHelper.append(spec)
          spec = ''
          continue 

        if check == True: 
          spec += vline
          continue
          
        res = matches_patternDeclare(vline.strip())
        if res == True and checkMemberHelper(gl, vline):
            #helper detected 
            check = True 
            spec += vline
   return retHelper


#AST for main program
def astForMainProgram(funcName, filename):
   ast = ''
   check = False
   with open(filename, "r") as file:
    for line in file:
        # Process each line
        vline = line
        if vline == "\n" and check == True:
          #print("AST for main program: ",ast)
          break

        if check == True: 
          ast += vline
          continue
          
        res = matches_patternDefinition(vline.strip())
        if res == True and funcName in vline:
            #helper detected 
            check = True 
            ast += vline
   return ast   

#main program spec
def vstSpecforMainFunction(funcName, filename):
   spec = ''
   check = False
   with open(filename, "r") as file:
    for line in file:
        # Process each line
        vline = line
        if vline == "\n" and check == True:
          break

        if check == True: 
          spec += vline
          continue
          
        res = matches_patternDeclare(vline.strip())
        if res == True and (funcName in vline):
            #helper detected 
            #print("vst spec helper detected")
            check = True 
            spec += vline
   return spec      
            

#main function   
if __name__ == '__main__':
  if len(sys.argv) != 2: 
    print("Please supply only the API Key")
    exit()
  OPENAI_API_KEY = sys.argv[1]
  client = OpenAI(api_key=OPENAI_API_KEY)

  prompt = '''"Translate the given specification to C program. Only include the C program in the content. No need to include a main function in the translated C program, \
    and other English description. There shouldn't be loops in the program. \
    All loops must be replaced by recursion. The only helper functions permitted are the ones provided with their signature, specification and English description preceeding it. \
    There shouldn't be any novel helper functions used in the program, other than built-in functions `malloc' and `free` if needed. You must assume that the result 
    of a malloc call is always successful (i.e., not NULL), i.e., your code does not have to check for NULL after a malloc call. 
    The necessary struct definitions will also be pre-provided, so the generated code should use the provided structure definitions, and not define new structs, or re-define the provded structs. \
    Additionally the program generated should not have any '#include' statements. Generate recursive code if and only if non-loopy code generation isn't possible. \
    There shouldn't be boolean returns of the form 'return (a == b)'. They should be replaced with 'if (a == b) then return true else return false' \
    The code must compile using clightgen. The user provides the specification, followed by the function name, followed by the function signature,  \
    the English description, two input output examples of program behaviour, and helper functions if any.  Do not generate characters like ``` that \ 
    makes the C-code not compile. 
    Here are two examples of what the user inputs look like and what your response should look like: 
    {Specification: "{x -> a * y -> b}{x -> b * y -> a}"},
    {Function Name: "swap"},
    {Function Signature: "void swap(int *x, int *y)"},
    {English Description: "The function swaps the values at *x and *y"},
    {I/O Example 1: "Input: (*x = 2, *y = 3), Output: (*x = 3, *y = 2)"},
    {I/O Example 2: "Input: (*x = 2, *y = 2), Output: (*x = 2, *y = 2)"},
    {Your Response: "void swap(int* x, int* y) {  int temp = *x; *x = *y; *y = temp;}"},
    {Specification: "{int a[], length = length of a, 0 <= index <= length}{(exists i:Z, index <= i < length -> a[i] = value) <-> true}"},
    {Function Name: "checkMember"},
    {Function Signature: "bool checkMember(int a[],int value,unsigned index,unsigned length)"},
    {English Description: "The function returns true if a[i] equals value, where i ranges from index to length - 1"},
    {I/O Example 1: "Input: a = {1,2,3,4,5} value = 3 index = 3 length = 5, Output: false"},
    {I/O Example 2: "Input: a = {1,2,3,4,5} value = 3 index = 1 length = 5, Output: true"},
    {Your Response: "bool checkMember(int a[],int value, unsigned index, unsigned length) \
     { if(index == length) {return false;} else if(a[i] == value) {return true;} else{return checkMember(a, value, index + 1, length);}"''' 

  
  filesiter = [f for f in os.listdir('specText')]
  premove = subprocess.run(["rm", "-rf", "proglogs", "prooflogs", "proverLLMSpec"], stderr=subprocess.PIPE)
  pcreate = subprocess.run(["mkdir", "proglogs", "prooflogs", "proverLLMSpec"], stderr=subprocess.PIPE)
  #filesiter = ['findMinNode.txt']
  #pdb.set_trace()  
  countiter = 0
  for file in filesiter:
    print("File: ",file, "Count: ",countiter)
    countiter += 1
    messages=[
      {"role": "developer", "content": prompt},
    ]
    lines = []
    with open("specText/"+file, "r") as f:
      lines = [line.strip() for line in f]
    #pdb.set_trace()
    start_time = time.perf_counter()
    uinp = 'Specification: '+lines[0]
    ufname = 'Function Name: '+lines[1]
    ufsig = 'Function Signature: '+lines[2]
    ufeng = 'English Description: '+lines[3]
    ufex1 = 'I/O Example 1: '+lines[4]
    ufex2 = 'I/O Example 2: '
    if len(lines) > 5:
      ufex2 = 'I/O Example 2: '+lines[5]
    uhelpers = 'No helpers allowed other than malloc and free'
    if len(lines) > 6: 
      uhelpers = "\n".join(lines[6:])
    #with open("helper.txt", "r") as file:
      #uhelpers = file.read()
    ustructs = "Structure definitions (Please use these definitions, and not define new structs, or re-define them in the code): struct sll {int key; struct sll *next;}, typedef struct sll **sllbox, struct tree {int key; int value; struct tree *left, *right;}, typedef struct tree **treebox"
    #unspec = input("Please enter the name of the specification file: ")
    #append all of the inputs to messages
    messages.append({"role":"user","content":uinp})
    messages.append({"role":"user","content":uhelpers})
    messages.append({"role":"user","content":ustructs})
    messages.append({"role":"user","content":ufname})
    messages.append({"role":"user","content":ufsig})
    messages.append({"role":"user","content":ufeng})
    messages.append({"role":"user","content":ufex1})
    messages.append({"role":"user","content":ufex2})
    #set of helpers allowed/permitted
    lfunc = ["f_dummylist", "f_dummylistc", "f_dummyTree"]
    hfunc = []
    #lfunc.append("f_" + ufname)
    unspecv = "proofs/" + file.split(".")[0] + ".v"
    flog = open("proglogs/" + lines[1] + ".txt", "w")
    cProgName = lines[1] + "C.c"
    #update lfunc with specs - specifciations of functions that are there? 
    with open(unspecv, "r") as file:
      for line in file:
        # Process each line
        vline = line.strip()
        res = matches_patternDeclare(vline)
        if res == True:
            fnames = vline.split(" ")
            fname = ''
            #get the name - all helper names  
            for fn in fnames: 
              if len(fn) > 0 and fn[0] == "_":
                fname = fn[1:] 
                break
            if lines[1] != fname:
              hfunc.append(fname)
            lfunc.append("f_" + fname)
    
    count_threshold = 0 
    while count_threshold < 10:
      flog.write("Program Generation attempt: "+str(count_threshold)+"\n")
      print(count_threshold)
      completion = client.chat.completions.create(
      model="gpt-5-mini-2025-08-07",
      seed=844321009,
      #temperature=0.8,
      messages=messages
      )

      cp2 = completion.choices[0].message.content
      cp1 = cp2.replace('```c','')
      cprog= cp1.replace('```','')
      fcprog = open(cProgName,"w") #generates the program
      fcprog.write('#include "treelistdef.c"')
      if len(lines) > 6:
        fcprog.write('\n')
        fcprog.write(uhelpers)
      fcprog.write('\n')
      fcprog.write(cprog)
      fcprog.close()

      #compile
      p = subprocess.run(["clightgen","-normalize",cProgName], stderr=subprocess.PIPE)
      #check if there are compilation errors
      if p.returncode != 0:
       strp = "Code does not compile - Please produce a compilable code. Syntax error: " + p.stderr.decode("utf-8")
       #print(strp)
       flog.write(strp+"\n")
       messages.append({"role":"user","content":strp})
       count_threshold += 1
      elif checkLoopsOrfName(unspecv) == False:
       stre = "Loops or novel helper functions detected - Please produce a code without the above."
       flog.write(stre+"\n")
       messages.append({"role":"user","content":stre})
       count_threshold += 1
      else:
        break

    if count_threshold == 10:
      print("Program Generation timed out")
      flog.write("Program Generation timed out\n")
      flog.close()
    else:
      
      flist = returnHelperSpecs(hfunc, unspecv)
      compcertast = astForMainProgram(lines[1], lines[1] + "C.v")
      vstspec = vstSpecforMainFunction(lines[1], unspecv)
      writeToBenchmarkFile(cprog, compcertast, vstspec, flist, lines[1] + ".txt")
      end_time = time.perf_counter()
      flog.write("Time taken: "+str(end_time - start_time)+" seconds\n")
      flog.close()
      #compile coq
      pcoq = subprocess.run(["coqc", "-Q", ".", "GenProof", lines[1] + "C.v"], stderr=subprocess.PIPE)
      #call GenProof
      p = subprocess.run(["python3", "genProof.py",sys.argv[1],lines[1] + ".v"], stderr=subprocess.PIPE)
      
      #run alectryon to output the respective json file








