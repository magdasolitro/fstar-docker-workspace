# F* with Docker: guide to installation

This repository contains the scripts to install F* easily, without having to go through a painful native installation. In the following sections, you will find the explanation of each and every step to start working with F*.

## Install Docker
The first thing to do is installing Docker: the page at https://docs.docker.com/get-docker/ provides you with a detailed guide to install it on whatever OS you're using. Remember to open Docker Desktop before you can run a Docker application! 

## Run scripts
Once you have a Docker Desktop open, run the script ```./install.sh```: this will install the Docker image of F* on your laptop. Afterwards, run ```./run.sh``` to activate the Docker container.

## Write your code
Now you can start playing with F*: write your programs in a ```.fst``` file and save them in the ```workspace/``` directory to execute them.

## Execute your code
To execute a program from the workspace, simply run the command ```fstar.exe <filename>.fst``` (replace <filename> with the actual name of the file, of course).
