/* This example is adopted from 
   https://www.geeksforgeeks.org/n-queen-problem-backtracking-3
*/

#define N 8
int board[N][N] = { {0, 0, 0, 0}, 
                    {0, 0, 0, 0}, 
                    {0, 0, 0, 0}, 
                    {0, 0, 0, 0} 
}; 
int numSols;  
  
/* A utility function to check if a queen can 
   be placed on board[row][col]. Note that this 
   function is called when "col" queens are 
   already placed in columns from 0 to col -1. 
   So we need to check only left side for 
   attacking queens */
int isSafe(int board[N][N], int row, int col) 
{ 
    int i, j; 
  
    /* Check this row on left side */
    for (i = 0; i < col; i++)
        if (board[row][i])
            return 0;
  
    /* Check upper diagonal on left side */
    for (i=row, j=col; i>=0 && j>=0; i--, j--)
        if (board[i][j])
            return 0;
  
    /* Check lower diagonal on left side */
    for (i=row, j=col; j>=0 && i<N; i++, j--)
        if (board[i][j])
            return 0;
  
    return 1; 
} 
  
/* A recursive utility function to solve N 
   Queen problem */
void solveNQUtil(int board[N][N], int col) 
{ 
    /* base case: If all queens are placed 
      then return true */
    if (col >= N) {
      ++numSols;
      return;
    }
      
    /* Consider this column and try placing 
       this queen in all rows one by one */
    for (int i = 0; i < N; i++) 
    { 
        /* Check if the queen can be placed on 
          board[i][col] */
        if ( isSafe(board, i, col) ) 
        { 
            /* Place this queen in board[i][col] */
            board[i][col] = 1; 
  
            /* recur to place rest of the queens */
            solveNQUtil(board, col + 1);
  
            /* If placing queen in board[i][col] 
               doesn't lead to a solution, then 
               remove queen from board[i][col] */
            board[i][col] = 0; // BACKTRACK 
        } 
    }   
} 
    
// driver program to test above function 
int main() 
{ 
    numSols = 0;
    solveNQUtil(board, 0);
    return numSols; 
} 
