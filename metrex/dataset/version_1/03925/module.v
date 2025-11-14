module TicTacToe(
    input clk,
    input reset,
    input player1_turn,
    input player2_turn,
    input [1:0] row,
    input [1:0] column,
    output reg game_over,
    output reg [1:0] winner,
    output reg tie,
    output reg [8:0] board
);

    reg [1:0] current_player;
    reg [8:0] game_board;
    reg [1:0] row_index;
    reg [1:0] col_index;
    reg [2:0] winner_index;
    reg [2:0] i;
    reg [2:0] j;
    
    always @(posedge clk) begin
        if (reset) begin
            current_player <= 2'b00;
            game_board <= 9'b000000000;
            row_index <= 2'b00;
            col_index <= 2'b00;
            winner_index <= 3'b000;
            i <= 3'b000;
            j <= 3'b000;
            game_over <= 1'b0;
            winner <= 2'b00;
            tie <= 1'b0;
            board <= game_board;
        end
        else begin
            // Update board if valid move
            if ((player1_turn && current_player == 2'b00) || 
                (player2_turn && current_player == 2'b01)) begin
                if (game_board[(row*3)+column] == 1'b0) begin
                    game_board[(row*3)+column] <= current_player + 1'b1;
                    board <= game_board;
                end
            end
            
            // Check for winner
            for (i = 0; i < 3; i = i + 1) begin
                // Check rows
                winner_index <= {i, 3'b000};
                if (game_board[(i*3)] == game_board[(i*3)+1] && 
                    game_board[(i*3)+1] == game_board[(i*3)+2] &&
                    game_board[(i*3)] != 1'b0) begin
                    game_over <= 1'b1;
                    winner <= game_board[(i*3)] - 1'b1;
                end
                // Check columns
                winner_index <= {3'b000, i};
                if (game_board[i] == game_board[i+3] && 
                    game_board[i+3] == game_board[i+6] &&
                    game_board[i] != 1'b0) begin
                    game_over <= 1'b1;
                    winner <= game_board[i] - 1'b1;
                end
            end
            // Check diagonals
            winner_index <= 3'b000;
            if (game_board[0] == game_board[4] && 
                game_board[4] == game_board[8] &&
                game_board[0] != 1'b0) begin
                game_over <= 1'b1;
                winner <= game_board[0] - 1'b1;
            end
            winner_index <= 3'b010;
            if (game_board[2] == game_board[4] && 
                game_board[4] == game_board[6] &&
                game_board[2] != 1'b0) begin
                game_over <= 1'b1;
                winner <= game_board[2] - 1'b1;
            end
            
            // Check for tie
            if (!game_over && !game_board[0] && !game_board[1] && !game_board[2] &&
                !game_board[3] && !game_board[4] && !game_board[5] &&
                !game_board[6] && !game_board[7] && !game_board[8]) begin
                game_over <= 1'b1;
                tie <= 1'b1;
            end
            
            // Update current player
            if (player1_turn && current_player == 2'b00) begin
                current_player <= 2'b01;
            end
            else if (player2_turn && current_player == 2'b01) begin
                current_player <= 2'b00;
            end
        end
    end
endmodule