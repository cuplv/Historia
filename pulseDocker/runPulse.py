import subprocess
import os

experiments = {

    "./testApps/ChatGPT_Benchmarks/EXN_bitmap_mishandling/app_bug/":"Bitmap Mishandling",
    "./testApps/ChatGPT_Benchmarks/EXN_configuration_changes/app_bug/":"Device Configuration",
    "./testApps/ChatGPT_Benchmarks/EXN_dialog_originally_created_here/app_bug/":"Dialog Origin",
    "./testApps/ChatGPT_Benchmarks/EXN_execute_twice/app_bug/":"Execute Twice",
    "./testApps/ChatGPT_Benchmarks/EXN_fragment_lifecycle/app_bug/":"Fragment Lifecycle",
    "./testApps/ChatGPT_Benchmarks/EXN_inefficient_network/app_bug/":"Inefficient Network",
    "./testApps/ChatGPT_Benchmarks/EXN_longRunningTask/app_bug/":"Long Running Task",
    "./testApps/ChatGPT_Benchmarks/EXN_activity_leak_noStatic/app_bug/": "Memory Leak",
    "./testApps/ChatGPT_Benchmarks/EXN_nullptr/app_bug/":"Null Pointer Exception",
    }

y = os.getcwd()
row_data = []
for x in list(experiments.keys()):
    os.chdir(x)
    clean = subprocess.check_output('./gradlew clean', shell=True)
    infer = subprocess.check_output("infer run --pulse -- ./gradlew build", shell = True)
    found_i = not ("No issues found" in infer.decode("utf-8"))
    clean = subprocess.check_output('./gradlew clean', shell=True) # Infer won't run again before cleaning
    pulse = subprocess.check_output("infer run --pulse-only -- ./gradlew build", shell = True)
    found_p = not ("No issues found" in pulse.decode("utf-8"))
    row_data.append((experiments[x], "yes" if found_i else "no" , "yes" if found_p else "no"))
    os.chdir(y)

print("%25s  %5s  %5s " % ("Experiment", "Infer", "Pulse") )
for r in row_data:
        print("%25s  %5s  %5s " % (r[0],r[1],r[2]))
