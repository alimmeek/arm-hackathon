#include <stdio.h>
#include <stdlib.h>


int max_file_size = 100;
int n_lines = 10;
int line_length = 10;
// actual is 100  x 100

/*
advent of code much

read file
start at top left i.e file[0][0]

finish at bottom right.

cost += file[line][index]

minimise cost, use A* or djikstras?

*/
// convert to int**


int* convert_list_of_strings_to_ints(char* ints_as_str){

    int* myints = malloc(sizeof(int) * line_length);
    for (int i=0;i<line_length;i++){
        myints[i] = (int) (ints_as_str[i] - '0');
    }
    return myints;
}

void print_graph(int** mygraph){
    for(int r=0; r<n_lines;r++){
        for(int c=0; c<line_length;c++){
            printf("%d," , mygraph[r][c]);
        }
        printf("\n");
    }
}




void parse_file_to_array(char* filename){

    FILE *fptr;
    fptr = fopen(filename,"r");
    
    int** graph = malloc(sizeof(int[n_lines][line_length]));

    char file_str[max_file_size];
    int curr_line = 0;

    while(fgets(file_str, max_file_size, fptr)) {
        printf("%s",file_str);
        graph[curr_line] = convert_list_of_strings_to_ints(file_str);

        curr_line+=1;
    }
    printf("\n");
    fclose(fptr);

    printf("File has %d lines and %d chars per line\n",n_lines,line_length);

    print_graph(graph);
    //mygraph->lines_length = lines_length;

}








int main(){
    
    parse_file_to_array("test1.txt");


    return 0;
}