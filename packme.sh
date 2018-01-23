#!/bin/bash

#TODO: put your student id here
STUDENTID=mn385914

zip $STUDENTID.zip CMakeLists.txt adorate.cpp blimit.hpp blimit.cpp  
mv $STUDENTID.zip ../sols/
