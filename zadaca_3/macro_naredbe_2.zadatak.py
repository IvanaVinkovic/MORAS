# -*- coding: utf-8 -*-
"""
Created on Mon Jan  9 10:06:29 2023

@author: Ivana
"""


def _macro_naredbe_(self, line, p, o):
    if line[0] != "$":
        return line     
    else:
        l = line[1:]
        if l == "END":
            return line  
        
        if "(" in l:
            x = l.split("(")
            temp = x[1].split(")")
        else:
            x = [l]
            temp = ""
        if "," in temp[0]:
            args = temp[0].split(",")
        else:
            args = temp[0]
        if x[0] == "MV":
            return "*@" + args[0] + " D=M M=0 @" + args[1] + " M=D"
        if x[0] == "SWP":
            return "*@" + args[0] + " D=M @temp M=D @" + args[1] + " D=M @" + args[0] + " M=D @temp D=M @" + args[1] + " M=D"
        if x[0] == "SUM":
            return "*@" + args[0] + " D=M @" + args[2] + " M=D @" + args[1] + " D=M @" + args[2] + " M=M+D"
        else:
            self._flag = False
            self._line = o
            self._errm = "Invalid macro"
            return ""