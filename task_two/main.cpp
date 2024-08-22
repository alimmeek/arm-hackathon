// C++ program
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <array>
using namespace std;

constexpr int n_lines=100;
constexpr int length_line = 100;


array<int,length_line> string_to_ints(string ints_as_str){
    // convert each char in the line to an int 
    array<int,length_line> ints;
    for(int i=0;i<length_line;i++){
        ints[i] = ints_as_str[i] - '0'; // convert char representation of int
    }
    return ints;
}

void print_cost(array<array< int,length_line>,n_lines> cost){
    for(int i=0;i<n_lines;i++){
    for(int j=0;j<length_line;j++){
            cout << cost[i][j] << " ,";
    }cout << endl;
    }
}


array<array< int,length_line>,n_lines> parse_file_to_matrix(string filename){
    // Wrapper for parsing file, and error handling


    array<array< int,length_line>,n_lines> matrix;
    ifstream inputFile(filename);

    // Error handling
    if (!inputFile.is_open()){
        cerr << "Error opening the file!" << endl;
        exit(1);
    }

    string line; // read from file into this string
    int curr_line = 0; 

    // Parse file to matrix
    while (getline(inputFile, line)) { 
        matrix[curr_line] = string_to_ints(line); // write ints to array
        curr_line +=1; 
    }
  
    // Close the file 
    inputFile.close(); 

    return matrix;
}

int minCost(array<array< int,length_line>,n_lines> cost){
    /*
    fold over matrix in 2D

    cost of current element += min (cost_above, cost_below) 

    overwrite the cost array for space efficiency 

    */
    //Cost of (0,0) already exists
    // cost of first column
    for (int i = 1; i < n_lines; i++)
        cost[i][0] += cost[i - 1][0];

    // cost of first row
    for (int j = 1; j < length_line; j++)
        cost[0][j] += cost[0][j - 1];

    //Process the rest of cost matrix
    // from 1,1 to bottom right
    for (int i = 1; i < n_lines; i++) {
        for (int j = 1; j < length_line; j++) {
            cost[i][j] += min({ cost[i - 1][j], // check above
                               cost[i][j - 1]}); // check to the left
        }
    }
    /*
    
                     |  c+=cost_left | c += cost_left ...
    _________________
      c+=cost_above  | c + min(cost_above, cost_left)
            .        | . . .  | .
            .        | . . .  | . .
            .        | . . .  | . . .

    
    
    */

    // Return the value in the bottom right cell
   // print_cost(cost);
    return cost[n_lines - 1][length_line - 1];
}



int main(){

    array<array< int,length_line>,n_lines> cost = parse_file_to_matrix("data.txt");
    int min = minCost(cost);
    cout << "Minimum cost: " << min << endl;
    return 0; 

}