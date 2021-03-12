import xml.etree.ElementTree as ET

class Result:

    def __init__(self, data):
        self.file = data
        self.tests = 0
        self.correct_positive = 0
        self.correct_negative = 0
        self.false_positive = 0
        self.false_negative = 0
        self.error  = 0
        self.unknown = 0
        self.name = ""
        self._process_file()
        self.is_run_definition = False

    def _process_file(self):
        root = ET.fromstring(self.file)
        try:
            self.name = root.attrib["block"]
        except:
            self.name = root.attrib["name"]
            self.is_run_definition = True
        # TODO: This can be heavily optimized with some maps instead of nested IF's
        for run in root.iter('run'):
            self.tests += 1
            try:
                is_positive = run.attrib["expectedVerdict"] == "true"
            except:
                is_positive = True
            for x in run.iter():
                try:
                    title = x.attrib["title"]
                except:
                    title = ""
                if title == "category":
                    category = x.attrib["value"]
                    if category == "correct":
                        if is_positive:
                            self.correct_positive += 1
                        else:
                            self.correct_negative += 1
                    elif category == "error":
                        self.error += 1
                    elif category == "unknown":
                        self.unknown += 1
                    elif category == "wrong":
                        if is_positive:
                            self.false_positive += 1
                        else:
                            self.false_negative += 1
                    else:
                        raise ValueError(f'{category} is not mapped')
                    break



    def get_correct(self):
        return (self.correct_positive + self.correct_negative)

    def get_wrong(self):
        return (self.false_positive + self.false_negative)

    def get_p_score(self):
        return self.correct_positive*2

    def get_n_score(self):
        return self.correct_negative

    def get_fp_score(self):
        return self.false_positive*(-32)

    def get_fn_score(self):
        return self.false_negative*(-16)

    def score_overall(self):
        return self.get_fn_score() + self.get_fp_score() + self.get_n_score() + self.get_p_score()

    def score_falsification(self):
        return self.get_n_score() + self.get_fn_score()


    def check_processing(self):
        return self.tests == (self.get_correct() + self.get_wrong() + self.error)


    def summary(self):
        return [str(self.name), str(self.tests), str(self.correct_positive), str(self.correct_negative),
            str(self.false_positive), str(self.false_negative), str(self.unknown), str(self.error)]

    def to_csv(self, separator):
        return separator.join(self.summary())

    def __repr__(self):
        return str(self.summary())

    def __lt__(self, other):
        magic_order = ["SoftwareSystems-uthash-MemSafety"
            ,"SoftwareSystems-OpenBSD-MemSafety"
            ,"SoftwareSystems-BusyBox-MemSafety"
            ,"MemSafety-Other"
            ,"MemSafety-LinkedLists"
            ,"MemSafety-Juliet"
            ,"MemSafety-Heap"
            ,"MemSafety-Arrays"
            ,"MemSafety-MemCleanup"
            ,"SoftwareSystems-uthash-ReachSafety"
            ,"SoftwareSystems-DeviceDriversLinux64-ReachSafety"
            ,"SoftwareSystems-DeviceDriversLinux64Large-ReachSafety"
            ,"SoftwareSystems-AWS-C-Common-ReachSafety"
            ,"ReachSafety-XCSP"
            ,"ReachSafety-Sequentialized"
            ,"ReachSafety-Recursive"
            ,"ReachSafety-ProductLines"
            ,"ReachSafety-Loops"
            ,"ReachSafety-Heap"
            ,"ReachSafety-Floats"
            ,"ReachSafety-ECA"
            ,"ReachSafety-ControlFlow"
            ,"ReachSafety-Combinations"
            ,"ReachSafety-BitVectors"
            ,"ReachSafety-Arrays"
            ,"ConcurrencySafety-Main"
            ,"Termination-Other"
            ,"Termination-MainHeap"
            ,"Termination-MainControlFlow"
            ,"SoftwareSystems-uthash-NoOverflows"
            ,"SoftwareSystems-BusyBox-NoOverflows"
            ,"NoOverflows-Other"
            ,"NoOverflows-BitVectors"]

        magic_number = len(magic_order)+1

        try:
            indexA = magic_order.index(self.name)
        except:
            indexA = magic_number

        try:
            indexB = magic_order.index(other.name)
        except:
            indexB = magic_number

        return indexA < indexB

from os import listdir, path
import bz2

class GetResults:

    @staticmethod
    def get_test_paths(root):
        return [x[:-4] for x in listdir(root) if ".xml.bz2" in x]

    @staticmethod
    def get_xml_contents(f, root):
        with bz2.BZ2File(path.join(root, f + ".bz2"), 'r') as zip:
            return zip.read()

    @staticmethod
    def get_all_categories_summary(root):
        # TODO: this can be parallel without much effort
        tests = GetResults.get_test_paths(root)
        files = [GetResults.get_xml_contents(x, root) for x in tests]
        parsed_files = [Result(x) for x in files]
        return [x for x in parsed_files]


def main():
    with open("output.csv", "w") as f:
        results = GetResults.get_all_categories_summary("results")
        results.sort()
        for x in results:
            if x.is_run_definition:
                continue
            f.write(x.to_csv("\t") + "\n")


if __name__ == "__main__":
    main()