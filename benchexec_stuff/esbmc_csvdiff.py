from tkinter import filedialog
from tkinter import *
import tkinter.ttk
import csv

class BenchexecRow:

    def __init__(self, benchmark, property, category, result):
        self.benchmark = benchmark
        self.property = property
        self.category = category
        self.result = result

    def to_str(self):
        return f'{self.benchmark} {self.result}'
    
    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.benchmark == other.benchmark and self.result == other.result
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class BenchexecCSVReader:

    @staticmethod
    def load_file(path):
        with open(path) as csv_file:
            csv_reader = csv.reader(csv_file, delimiter='\t')
            rows = []
            for row in csv_reader:
                rows.append(BenchexecRow(row[0],row[1], row[2], row[3]))
            return rows


class Application:
    def __init__(self, master=None):
        self.master = master
        
        self.setup_header_container()
        self.setup_csv1_container()
        self.setup_csv2_container()
        self.setup_output_container()        
    
    def setup_header_container(self):
        self.header_container = Frame(self.master)
        self.header_container["pady"] = 10
        self.header_container.pack()

        self.header_container_label = Label(self.header_container, text="Benchexec CSV diff")
        self.header_container_label.pack()

    def setup_csv1_container(self):
        self.csv1_container = Frame(self.master)
        self.csv1_container["padx"] = 10
        self.csv1_container.pack()

        self.csv1_filepicker =  Button(self.csv1_container)
        self.csv1_filepicker["text"] = "CSV 1"
        self.csv1_filepicker["command"] = self.setup_file1
        self.csv1_filepicker.pack(side=LEFT)

        self.csv1_entrypoint = Entry(self.csv1_container)
        self.csv1_entrypoint.pack(side=RIGHT)

    def setup_file1(self):
        self.csv1 = filedialog.askopenfilename(title = "Select file")
        self.csv1_entrypoint.insert(0, self.csv1)
        
    def setup_csv2_container(self):
        self.csv2_container = Frame(self.master)
        self.csv2_container["padx"] = 10
        self.csv2_container.pack()

        self.csv2_filepicker =  Button(self.csv2_container)
        self.csv2_filepicker["text"] = "CSV 2"
        self.csv2_filepicker["command"] = self.setup_file2
        self.csv2_filepicker.pack(side=LEFT)

        self.csv2_entrypoint = Entry(self.csv2_container)
        self.csv2_entrypoint.pack(side=RIGHT)

    def setup_file2(self):
        self.csv2 = filedialog.askopenfilename(title = "Select file")
        self.csv2_entrypoint.insert(0, self.csv2)

    def setup_output_container(self):
        self.output_container = Frame(self.master)
        self.output_container["padx"] = 10
        self.output_container["pady"] = 10
        self.output_container.pack()

        self.output_button = Button(self.output_container)
        self.output_button["text"] = "Compare CSV's"
        self.output_button["command"] = self.compare_csv
        self.output_button.pack()

        self.var_output = DoubleVar()
        self.output_progress = tkinter.ttk.Progressbar(self.output_container, variable=self.var_output, maximum=100)
        self.output_progress.pack()

        self.output_text = Text(self.output_container, width=90, height=10)
        self.output_text.pack()

    def compare_csv(self):
        csv1_list = BenchexecCSVReader.load_file(self.csv1)
        self.var_output.set(10)
        self.master.update()

        csv2_list = BenchexecCSVReader.load_file(self.csv2)        
        self.var_output.set(20)
        self.master.update()

        diff = [x for x in csv2_list if x not in csv1_list]        
        self.var_output.set(80)
        self.master.update()
        for x in diff:
            self.output_text.insert(END, x.to_str() + "\n")
        
        self.var_output.set(100)
        self.master.update()


root = Tk()
Application(root)
root.mainloop()

