#!/usr/bin/env python3

import xml.etree.ElementTree as ET
import os

class Utils:
    @staticmethod
    def fixpath(path):
        return os.path.abspath(os.path.expanduser(path))

class TestcaseParser:
    """
    Parse a Testcase File
    """

    def get_values(self, test_file):
        tree = ET.parse(Utils.fixpath(test_file))
        root = tree.getroot()
        return [x.text for x in root.iter("input")]

class SourceCodeAppend:

    @staticmethod 
    def _get_array_string(values):
        start = "double __TEST2C_ARRAY[__TEST2C_ARRAY_LENGTH] = {"
        contents = ','.join(values)
        end = "};"
        return f"{start}{contents}{end}" 

    @staticmethod
    def _get_definitions(values):
        return f"""
#include <stdlib.h>
#include <sysexits.h>
#define __TEST2C_ARRAY_LENGTH {len(values)}
{SourceCodeAppend._get_array_string(values)}
            """
    @staticmethod
    def _get_nondet_definitions():
        return """
size_t __TEST2C_COUNTER = 0;
double __TEST2C_nondet() {
        if(__TEST2C_COUNTER == __TEST2C_ARRAY_LENGTH) exit(EX_DATAERR); 
        return __TEST2C_ARRAY[__TEST2C_COUNTER++];
}

int __VERIFIER_nondet_int() { return (int) __TEST2C_nondet(); }
unsigned int __VERIFIER_nondet_uint() { return (unsigned int) __TEST2C_nondet(); }
            """

    @staticmethod
    def get(values):
        top = SourceCodeAppend._get_definitions(values)
        bottom = SourceCodeAppend._get_nondet_definitions()
        return f"{top} {bottom}"
