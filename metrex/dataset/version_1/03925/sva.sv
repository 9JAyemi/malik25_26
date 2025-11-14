// SVA checker for TicTacToe. Bind into DUT for assertions and coverage.
module TicTacToe_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        player1_turn,
  input  logic        player2_turn,
  input  logic [1:0]  row,
  input  logic [1:0]  column,
  input  logic        game_over,
  input  logic [1:0]  winner,
  input  logic        tie,
  input  logic [8:0]  board,

  // Internals (bound)
  input  logic [1:0]  current_player,
  input  logic [8:0]  game_board
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Helpers
  function automatic int idx(input logic [1:0] r, input logic [1:0] c);
    return (r*3)+c;
  endfunction
  function automatic logic [8:0] bitmask(input int k);
    return (9'b1 << k);
  endfunction
  function automatic bit row_win(input logic [8:0] b);
    return ((b[0]==b[1] && b[1]==b[2] && b[0]!=0) ||
            (b[3]==b[4] && b[4]==b[5] && b[3]!=0) ||
            (b[6]==b[7] && b[7]==b[8] && b[6]!=0));
  endfunction
  function automatic bit col_win(input logic [8:0] b);
    return ((b[0]==b[3] && b[3]==b[6] && b[0]!=0) ||
            (b[1]==b[4] && b[4]==b[7] && b[1]!=0) ||
            (b[2]==b[5] && b[5]==b[8] && b[2]!=0));
  endfunction
  function automatic bit diag_win(input logic [8:0] b);
    return ((b[0]==b[4] && b[4]==b[8] && b[0]!=0) ||
            (b[2]==b[4] && b[4]==b[6] && b[2]!=0));
  endfunction
  function automatic bit any_win(input logic [8:0] b);
    return row_win(b) || col_win(b) || diag_win(b);
  endfunction
  function automatic bit full(input logic [8:0] b);
    return &b;
  endfunction

  // Environment constraints
  assume property (!(player1_turn && player2_turn));
  assume property ((player1_turn || player2_turn) |-> (row < 3 && column < 3));

  // Reset values (visible 1 cycle after reset rises)
  assert property ($rose(reset) |=> current_player==2'b00 && game_board==9'b0 &&
                              game_over==0 && winner==2'b00 && tie==0 && board==9'b0);

  // Turn gating: only accept moves on the correct player's turn
  assert property ((player1_turn && current_player==2'b00) ||
                   (player2_turn && current_player==2'b01) ||
                   !(player1_turn || player2_turn));

  // Successful move: empty cell -> set that cell, board latches previous game_board, and turn advances
  assert property (
    ( (player1_turn && current_player==2'b00) && (row<3 && column<3) &&
      (game_board[idx(row,column)]==0) )
    |=> (game_board == ($past(game_board) | bitmask($past(idx(row,column))))) &&
        (board      == $past(game_board)) &&
        (current_player == 2'b01)
  );
  assert property (
    ( (player2_turn && current_player==2'b01) && (row<3 && column<3) &&
      (game_board[idx(row,column)]==0) )
    |=> (game_board == ($past(game_board) | bitmask($past(idx(row,column))))) &&
        (board      == $past(game_board)) &&
        (current_player == 2'b00)
  );

  // No overwrite: occupied cell -> no board change and turn must NOT advance
  assert property (
    ( (player1_turn && current_player==2'b00) && (row<3 && column<3) &&
      (game_board[idx(row,column)]==1) )
    |=> (game_board == $past(game_board)) &&
        (board      == $past(board)) &&
        (current_player == $past(current_player))
  );
  assert property (
    ( (player2_turn && current_player==2'b01) && (row<3 && column<3) &&
      (game_board[idx(row,column)]==1) )
    |=> (game_board == $past(game_board)) &&
        (board      == $past(board)) &&
        (current_player == $past(current_player))
  );

  // Board monotonicity: cells never clear without reset
  genvar g;
  generate
    for (g=0; g<9; g++) begin : MONO
      assert property (!$fell(game_board[g]));
      assert property (!$fell(board[g]));
    end
  endgenerate

  // Win detection: if previous state had a win, game_over must assert next cycle
  assert property ( any_win($past(game_board)) |=> game_over );

  // No spurious game_over: without a win and not full, must not assert game_over next cycle
  assert property ( !any_win($past(game_board)) && !full($past(game_board)) |=> !game_over );

  // Tie semantics (intended): if board becomes full without a win, tie and game_over must assert next cycle
  assert property ( full($past(game_board)) && !any_win($past(game_board)) |=> game_over && tie );

  // Tie implies game over and no winner
  assert property ( tie |-> game_over && winner==2'b00 );

  // Once game_over, outputs freeze until reset
  assert property ( game_over |=> game_over );
  assert property ( game_over |=> $stable(board) && $stable(game_board) && $stable(winner) && $stable(tie) && $stable(current_player) );

  // Cover: basic scenarios
  cover property (player1_turn && current_player==2'b00 && (row<3 && column<3) && game_board[idx(row,column)]==0);
  cover property (player2_turn && current_player==2'b01 && (row<3 && column<3) && game_board[idx(row,column)]==0);
  cover property ( any_win(game_board) );
  cover property ( full(game_board) && !any_win(game_board) ##1 tie && game_over );

endmodule

// Bind into the DUT (connect internals)
bind TicTacToe TicTacToe_sva u_TicTacToe_sva (
  .clk          (clk),
  .reset        (reset),
  .player1_turn (player1_turn),
  .player2_turn (player2_turn),
  .row          (row),
  .column       (column),
  .game_over    (game_over),
  .winner       (winner),
  .tie          (tie),
  .board        (board),
  .current_player (current_player),
  .game_board     (game_board)
);