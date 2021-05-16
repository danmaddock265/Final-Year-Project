# User Guide

## Environment
A Linux environment must be used to run this project.



## Setting up Coq and SSReflect
### The steps for setting up Coq:
1.	Install opam on the machine. A guide for this can be found [here](https://opam.ocaml.org/doc/Install.html).

2.	Using a new terminal, initialise opam using the command: 
```
opam init
```

3.	Next, run these commands to list system packages that willneed to be installed in order for Coq to work:
```
opam install opam-depext 
opam-depext coq 
```


4.	After installing any needed system packages, use these commands to install Coq and the GUI CoqIDE:
'''
opam apt-get install coq
opam apt-get install coqide
'''

5.	Run CoqIDE through the command :
```
coqide
```

### The steps for installing SSReflect.
1.	First, add the repository to opam using the command:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```

2.	Then, use the command 
```
opam install coq-mathcomp-ssreflect
```

3.	Restart CoqIDE if needed.



## Running the application:
Once a file has been opened in Coq, there will be five buttons on the top task bar that will be used to control the running of the program. 

![Coq Buttons](Pictures/CoqGuide.png)


From left to right:
-	Forward one command
-	Backward one command
-	Go to cursor (Runs program up until the point selected by the cursor)
-	Restart (go to beginning)
-	Go to end (Run the entire program at once)
