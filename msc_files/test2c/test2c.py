#!/usr/bin/env python3

import xml.etree.ElementTree as ET
import sys
from shutil import copyfile
import os
import subprocess

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

unsigned short __VERIFIER_nondet_ushort() { return (unsigned short) __TEST2C_nondet(); }
unsigned __VERIFIER_nondet_unsigned() { return (unsigned) __TEST2C_nondet(); }
unsigned long __VERIFIER_nondet_ulong() { return (unsigned long) __TEST2C_nondet(); }
unsigned char __VERIFIER_nondet_uchar() { return (unsigned char) __TEST2C_nondet(); }
unsigned int __VERIFIER_nondet_u32() { return (unsigned int) __TEST2C_nondet(); }
size_t __VERIFIER_nondet_size_t() { return (size_t) __TEST2C_nondet(); }
short __VERIFIER_nondet_short() { return (short) __TEST2C_nondet(); }
//sector_t __VERIFIER_nondet_sector_t() { return (sector_t) __TEST2C_nondet(); }
pthread_t __VERIFIER_nondet_pthread_t() { return (pthread_t) __TEST2C_nondet(); }
//char* __VERIFIER_nondet_pchar() { return (char*) __TEST2C_nondet(); }
_Bool __VERIFIER_nondet_bool() { return (_Bool) __TEST2C_nondet(); }
loff_t __VERIFIER_nondet_loff_t() { return (loff_t) __TEST2C_nondet(); }
int __VERIFIER_nondet_int() { return (int) __TEST2C_nondet(); }
unsigned int __VERIFIER_nondet_uint() { return (unsigned int) __TEST2C_nondet(); }
long __VERIFIER_nondet_long() { return (long) __TEST2C_nondet(); }
double __VERIFIER_nondet_double() { return (double) __TEST2C_nondet(); }
float __VERIFIER_nondet_float() { return (float) __TEST2C_nondet(); }
char __VERIFIER_nondet_char() { return (char) __TEST2C_nondet(); }
            """

    @staticmethod
    def get(values):
        top = SourceCodeAppend._get_definitions(values)
        bottom = SourceCodeAppend._get_nondet_definitions()
        return f"{top} {bottom}"


class Validation:
    """
        Create a validation procedure
    """

    def __init__(self):
        self.has_executed = False
        self.reached_error = False

    def validate(self):
        raise NotImplementedError()


class ClangSanitizer(Validation):
    """
        Create a validation procedure
    """

    #ENV_OPTIONS = "ASAN_OPTIONS=detect_leaks=1" # Makes asan detect leaks on macOS (required). It is enabled by default for Linux
    COMMAND = ["clang", "-O1", "-g", "-fsanitize=address", "output.c"] # I am not sure if -g is required
    def validate(self):
        print("Evaluating test - Address Sanitizer")
        p = subprocess.Popen(self.COMMAND)
        p.wait()
        print("Running test - Address Sanitizer")
        q = subprocess.Popen("./a.out")
        q.wait()
        if(q.returncode != 0):
            return False
        return True



def main(c_program, testcase, output="output.c"):
    copyfile(Utils.fixpath(c_program), output)
    with open(output, 'a') as f:
        bottom = SourceCodeAppend.get(TestcaseParser().get_values(testcase))
        f.write(bottom)

if __name__ == "__main__":
    print("Starting test case generation")
    main(sys.argv[1], sys.argv[2])
