
# Installation
1. Install Fortress so that it can be accessed from the command line as `fortress`
2. Clone this git repository
3. run `git submodule init` to pull the testrunner files
4. Create a virtual python environment `python3 -m venv venv`
5. Activate the virtual environment `source venv/bin/activate`
6. Update the pip package manager `pip install --upgrade pip`
6. Install python dependencies `pip install -r testrunner/requirements.txt`
4. Download the non-incremental UFNIA benchmark from [https://zenodo.org/records/11061097] and unzip it as a sibling to this directory. (Direct link[https://zenodo.org/records/11061097/files/UFNIA.tar.zst])
    - `cd ..` to go one level above this directory
    - `wget https://zenodo.org/records/11061097/files/UFNIA.tar.zst` will download the zipped tar file
    - `tar --zstd -xvf UFNIA.tar.zst` will unzip the tar file to the directory `non-incremental`
5. Collect the list of all possible test files by running `python3 find_all_files.py`.
    - If you have downloaded the benchmark other than as  a sibling to this directory, you may provide it as an additional argument to `find_all_files.py`.  
    - We avoid the the subdirectory `vcc-havoc` as it contains integers constants outside the 32 bit range (which Fortress does not support), and the `full`, `partial`, and `qf` subdirectories of `2019-Preiner` so as to not weight our tested files x4 towards the different implementations of the same problem.
6. Create a random subset of tests to administer. Use `python3 make_random_subset.py --seed 1` to generate the same set we used.
7. Run the test suite `python3 run_sat_tests.py`. You can use the `--help` option to list ways to customize the execution of this script
    