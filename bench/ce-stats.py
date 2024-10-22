#!/usr/bin/env python

# Helper script to compute statistics about checking counterexamples.

# The script creates 4 files:
# - [export_file_raw], a CSV file with columns date / file / prover /
#   verdict / concrete_RAC / abstract_RAC for each CE that is checked
# - [export_file], the same data aggregated according to the verdict
# - [export_file_incomplete_small_step], only the data corresponding
#   to incomplete verdicts, grouped by small-step RAC result
# - [export_file_incomplete_giant_step], only the data corresponding
#   to incomplete verdicts, grouped by giant-step RAC result

from datetime import date
import os
import pandas as pd
import re

dir = "./bench/check-ce/oracles"
export_file_raw = "./data_raw.csv"
export_file = "./data.csv"
export_file_incomplete_small_step = "./data_incomplete_small_step.csv"
export_file_incomplete_giant_step = "./data_incomplete_giant_step.csv"

rx_model = re.compile(r"Selected model [0|1]: (?P<v>[A-Z_]*)\n")
rx_concrete_RAC = re.compile(r"Concrete RAC: (?P<c>[A-Z_]*)(?P<cr>.*)\n")
rx_abstract_RAC = re.compile(r"Abstract RAC: (?P<a>[A-Z_]*)(?P<ar>.*)\n")

rx_dict_incomplete = {
    "cannot decide post": re.compile(r"(.*)Postcondition of (.*) cannot be evaluated(.*)"),
    "cannot decide pre": re.compile(r"(.*)Precondition of (.*) cannot be evaluated(.*)"),
    "cannot decide": re.compile(r"(.*)cannot be evaluated(.*)"),
    "cannot import": re.compile(r"(.*)cannot import value(.*)"),
    "cannot evaluate builtin": re.compile(r"(.*)cannot evaluate builtin(.*)"),
    "missing return value": re.compile(r"(.*)missing value for return value(.*)"),
    "many args for exec": re.compile(r"(.*)many args for exec fun(.*)"),
    "uncaught exception": re.compile(r"(.*)uncaught exception(.*)"),
    "undefined argument": re.compile(r"(.*)undefined argument(.*)"),
    "unexpected arguments": re.compile(r"(.*)unexpected arguments(.*)"),
    "missing global": re.compile(r"(.*)missing value for global(.*)"),
}
list_of_verdicts = [
    "INCOMPLETE",
    "NC",
    "BAD_CE",
    "NC_SW",
    "SW",
]

rx_filepath = re.compile(r"bench/check-ce/oracles/(?P<f>[a-zA-Z0-9-_]*)_(?P<p>[a-zA-Z0-9,.\-]*)_[W|S]P.oracle")

def _parse_line(line,rx):
    match = rx.search(line)
    if match:
        return match
    return None

def _parse_reason(reason, rx_dict):
    for key, rx in rx_dict.items():
        match = rx.search(reason)
        if match:
            return key
    print ("WARNING! Unknown reason: " + reason)
    return reason

def _add_reason(res, reason, rx_dict):
    if res in ["FAILURE", "NORMAL", "STUCK"]:
        return res
    elif res in ["INCOMPLETE"]:
        return (res + " " + _parse_reason(reason, rx_dict))
    else:
        print("WARNING! Unknown RAC result: " + res)
        return res


def parse_file(filepath, data, date):
    # print("entering parse_file with filepath=" + filepath)
    with open(filepath, "r") as file_object:
        filepath = _parse_line(filepath,rx_filepath)
        if filepath is not None:
            file = filepath.group("f")
            prover = filepath.group("p")
            line = file_object.readline()
        else:
            print("WARNING! Could not parse filepath")
        while line:
            match = _parse_line(line,rx_model)
            if match is not None:
                verdict = match.group("v")
                line = file_object.readline()
                match_concrete = _parse_line(line,rx_concrete_RAC)
                line = file_object.readline()
                match_abstract = _parse_line(line,rx_abstract_RAC)
                if (match_concrete is not None) & (match_abstract is not None):
                    concrete_RAC = match_concrete.group("c")
                    reason_concrete = match_concrete.group("cr")
                    abstract_RAC = match_abstract.group("a")
                    reason_abstract = match_abstract.group("ar")
                    if verdict in list_of_verdicts:
                        concrete_RAC = _add_reason(concrete_RAC, reason_concrete, rx_dict_incomplete)
                        abstract_RAC = _add_reason(abstract_RAC, reason_abstract, rx_dict_incomplete)
                    else:
                        print("WARNING! Unknown verdict: " + verdict)
                    data.append(
                        {
                            "date": date,
                            "file": file,
                            "prover": prover,
                            "verdict": verdict,
                            "concrete_RAC": concrete_RAC,
                            "abstract_RAC": abstract_RAC,
                        }
                    )
            line = file_object.readline()

data = []
date = date.today()
print(date)
for filename in os.listdir(dir):
    f = os.path.join(dir, filename)
    if os.path.isfile(f):
        if f.endswith(".oracle"):
            parse_file(f, data, date.strftime("%Y%m%d"))
data = pd.DataFrame(data)
data.to_csv(export_file_raw, mode="w", header=True)

agg_data = data.groupby("date")["verdict"].value_counts().rename("nb")
agg_data = pd.DataFrame(agg_data)
agg_data.to_csv(export_file, mode="w", header=True)

agg_data_incomplete_small_step = data.query('verdict == "INCOMPLETE"').groupby("date")["concrete_RAC"].value_counts().rename("nb")
agg_data_incomplete_small_step = pd.DataFrame(agg_data_incomplete_small_step)
agg_data_incomplete_small_step.to_csv(export_file_incomplete_small_step, mode="w", header=True)

agg_data_incomplete_giant_step = data.query('verdict == "INCOMPLETE"').groupby("date")["abstract_RAC"].value_counts().rename("nb")
agg_data_incomplete_giant_step = pd.DataFrame(agg_data_incomplete_giant_step)
agg_data_incomplete_giant_step.to_csv(export_file_incomplete_giant_step, mode="w", header=True)
