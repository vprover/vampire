#include <iostream>
#include <thread>
#include <chrono>


#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include "Vampire.hpp"

using namespace std::chrono_literals;

int main(int argc, char* argv[]) {
    std::string theory;
    {
        std::ifstream file(argv[1]);
        if (!file) {
            std::cerr << "Failed to open file." << std::endl;
            return 1;
        }
        std::stringstream buffer;
        buffer << file.rdbuf(); // Read the whole file into the buffer
        theory = buffer.str(); // Get the string from the buffer
    }

    // Step 1: Initialize Vampire
    Vampire::init();

    // Step 2: Load theory
    if (!Vampire::loadTPTP("argv[1]-theory",theory)) {
        std::cerr << "Failed to load theory!" << std::endl;
        return 1;
    }

    {
        std::cout << "Vampire::listTheories()[0] " << Vampire::listTheories()[0] << std::endl;
    }

    // Step 3: Start the prover
    std::string query = "";
    std::string config = "-t 5 -s 1011 -p off";
    if (!Vampire::runProver(query, config)) {
        std::cerr << "Prover did not start (already running?)" << std::endl;
        return 1;
    }

    // Step 4: Start status polling thread
    std::thread([]() {
        while (true) {
            auto status = Vampire::getStatus();
            std::cout << "Status: ";
            switch (status) {
                case Vampire::ProverStatus::READY:
                    std::cout << "READY";
                    break;
                case Vampire::ProverStatus::RUNNING:
                    std::cout << "RUNNING";
                    break;
                case Vampire::ProverStatus::SUCCEEDED:
                    std::cout << "SUCCEEDED";
                    break;
                case Vampire::ProverStatus::FAILED:
                    std::cout << "FAILED";
                    break;
                case Vampire::ProverStatus::SIGNALLED:
                    std::cout << "SIGNALLED (signal = " << Vampire::lastSignal() << ")";
                    break;
                case Vampire::ProverStatus::ERROR:
                    std::cout << "ERROR";
                    break;
            }
            std::cout << std::endl;

            if (status != Vampire::ProverStatus::RUNNING) {
                std::cout << "--- Prover Output ---" << std::endl;
                std::cout << Vampire::getSolution() << std::endl;
                break;
            }

            std::this_thread::sleep_for(1s);
        }
    }).detach();

    // Keep main thread alive until monitoring thread finishes
    // Simple blocking wait
    std::this_thread::sleep_for(10s); // increase if your prover takes longer
    std::cout << "Main thread done." << std::endl;
    return 0;
}