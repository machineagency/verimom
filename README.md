# Verimom

Final project for CSE 507: Computer-Aided Reasoning for Software.

## Contents

`plotter/` contains an interpreter for the Verimom language. This is old code,
before I changed my direction.

`twohead/` contains all the current code for the project.

## Running Tests

Test programs are located in `example_progs.py`.
Add more tests there if you like.
To run equivalence and performance tests, run `python analyzer.py`.
Uncomment any tests at the bottom of that file.
To run the synthesizer, run `python synthesizer.py`.
At the bottom of `synthesizer.py` edit the program name that the `Rewrite`
constructor is called on.
As stated in the project report, unfortunately the synthesizer is
currently outputting garbage.

