# Specify the minimum version for CMake
cmake_minimum_required(VERSION 3.10)

# Project's name
project(main)

# Set the C++ standard
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# Please change the path to your g++-14 compiler
set(CMAKE_CXX_COMPILER "/opt/homebrew/bin/g++-14")

find_package(Clingo REQUIRED)

# Add compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -O2")

# Add the executable
add_executable(main main.cpp preprocessing.cpp basics.cpp Helper.cpp InvEncoder.cpp InvRefiner.cpp Solver2.cpp StringProcessor.cpp CounterexampleHandler.cpp)

# Include directories for the compiler
target_include_directories(main PRIVATE ${CMAKE_CURRENT_SOURCE_DIR} ~/miniconda3/envs/test/include)

target_link_libraries(main PRIVATE libclingo)