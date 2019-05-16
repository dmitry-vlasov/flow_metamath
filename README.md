# flow_metamath
[Metamath](http://us.metamath.org/) implementation in [flow9](https://github.com/area9innovation/flow9) language

1.  Make sure, that python, java and jre is installed on your machine

2.  Check out flow9 repository with something like

	    git clone https://github.com/area9innovation/flow9

3.  Add `flow9/bin` to your path. We also require 64-bit Java Runtime and Python in your path.

4.  Check out this repository, change directory to its root

5. Build metamath.jar with command:

    `build-with-flowc1 file=metamath.flow`

6. Run a test file with command:

    `java -jar metamath.jar file=uset-100000.mm`

