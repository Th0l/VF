#include <stdio.h>

int main(int argc, char *argv[]){
  int matrix[4][4];

  //matrix[0][0] = 0;
  //matrix[0][1] = 1;
  //matrix[0][2] = 2;
  //matrix[0][3] = 3;

  //matrix[1][0] = 1;
  //matrix[2][0] = 2;
  //matrix[3][0] = 3;

  matrix[1][1] = 2;
  matrix[1][2] = 3;
  matrix[1][3] = 4;

  matrix[2][1] = 3;
  matrix[2][2] = 4;
  matrix[2][3] = 5;

  matrix[3][1] = 4;
  matrix[3][2] = 5;
  matrix[3][3] = 6;

  for(int i = 1; i<4 ;i++){
    for(int j = 1; j<4 ;j++){
      printf("I:%d J:%d Sum:%d\n",i,j,matrix[i][j]);
    }
  }
}
