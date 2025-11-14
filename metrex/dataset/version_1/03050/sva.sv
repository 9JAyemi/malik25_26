// SVA bind module for DUT "word"
// Checks functional mapping and X-behavior; provides concise coverage.
module word_sva(
  input  [4:0] row,
  input  [4:0] col,
  input  [1:0] select,
  input        word
);

  // Sampling event on any input change
  event comb_ev;
  always @(row or col or select) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Golden lookup for expected 20-bit line; returns 'x when undefined
  function automatic [19:0] exp_data(input [1:0] sel, input [4:0] r);
    unique case (sel)
      2'b00: unique case (r)
        5'd0:  exp_data = 20'b00000000000000000000;
        5'd1:  exp_data = 20'b00000111111111100000;
        5'd2:  exp_data = 20'b00011000000000011000;
        5'd3:  exp_data = 20'b00100000000000000100;
        5'd4:  exp_data = 20'b01000111000011100010;
        5'd5:  exp_data = 20'b01001000100100010010;
        5'd6:  exp_data = 20'b01000000000000000010;
        5'd7:  exp_data = 20'b01000100000000100010;
        5'd8:  exp_data = 20'b00100011111111000100;
        5'd9:  exp_data = 20'b00011000000000011000;
        5'd10: exp_data = 20'b00000111111111100000;
        5'd11: exp_data = 20'b00000000000000000000;
        5'd12: exp_data = 20'b00000000000000000000;
        5'd13: exp_data = 20'b00011111000011110000;
        5'd14: exp_data = 20'b00100000000100001000;
        5'd15: exp_data = 20'b00100000001000000100;
        5'd16: exp_data = 20'b00100111101000000100;
        5'd17: exp_data = 20'b00100011000100001000;
        5'd18: exp_data = 20'b00011110000011110000;
        5'd19: exp_data = 20'b00000000000000000000;
        default: exp_data = 20'hx;
      endcase
      2'b01: unique case (r)
        5'd0:  exp_data = 20'b00000000000000000000;
        5'd1:  exp_data = 20'b00100011101110111000;
        5'd2:  exp_data = 20'b00100010101000100000;
        5'd3:  exp_data = 20'b00100010101110111000;
        5'd4:  exp_data = 20'b00100010100010100000;
        5'd5:  exp_data = 20'b00111011101110111000;
        5'd6:  exp_data = 20'b00000000000000000000;
        5'd7:  exp_data = 20'b00001110000001110000;
        5'd8:  exp_data = 20'b00011111000011111000;
        5'd9:  exp_data = 20'b00011111110001111000;
        5'd10: exp_data = 20'b00001111100111110000;
        5'd11: exp_data = 20'b00000011110001100000;
        5'd12: exp_data = 20'b00000001100001000000;
        5'd13: exp_data = 20'b00000000100000000000;
        5'd14: exp_data = 20'b00011110000000000000;
        5'd15: exp_data = 20'b00100000111100100100;
        5'd16: exp_data = 20'b00011100100010100100;
        5'd17: exp_data = 20'b00000010111100011100;
        5'd18: exp_data = 20'b00000010100010000100;
        5'd19: exp_data = 20'b00111100100010011000;
        default: exp_data = 20'hx;
      endcase
      2'b10: exp_data = 20'hx; // always undefined per DUT
      2'b11: unique case (r)
        5'd0:  exp_data = 20'b00000000000000101010;
        5'd1:  exp_data = 20'b00001000010000101010;
        5'd2:  exp_data = 20'b00111100111100110110;
        5'd3:  exp_data = 20'b01100111100110000000;
        5'd4:  exp_data = 20'b01000011000110011100;
        5'd5:  exp_data = 20'b00110000001100001000;
        5'd6:  exp_data = 20'b00011100111000011100;
        5'd7:  exp_data = 20'b00000111100000000000;
        5'd8:  exp_data = 20'b00000011000000110100;
        5'd9:  exp_data = 20'b00000010000000101100;
        5'd10: exp_data = 20'b00000000000000100100;
        5'd11: exp_data = 20'b00111000001110000001;
        5'd12: exp_data = 20'b01000100010001000001;
        5'd13: exp_data = 20'b01000100010001000010;
        5'd14: exp_data = 20'b01000100010001000010;
        5'd15: exp_data = 20'b01000100010001000100;
        5'd16: exp_data = 20'b01000100010001000100;
        5'd17: exp_data = 20'b01000100010001001000;
        5'd18: exp_data = 20'b01000100010001001000;
        5'd19: exp_data = 20'b00111001001110010000;
        default: exp_data = 20'hx;
      endcase
      default: exp_data = 20'hx;
    endcase
  endfunction

  // Assertions

  // When mapping is defined, col must be in range
  property legal_col_when_defined;
    (exp_data(select,row) !== 20'hx) |-> (col <= 5'd19);
  endproperty
  assert property (legal_col_when_defined)
    else $error("word: col out of range (>%0d) while mapping defined: col=%0d", 19, col);

  // When mapping is defined and col legal, word must match expected bit and be known
  property word_matches_expected;
    (exp_data(select,row) !== 20'hx && col <= 5'd19)
      |-> (! $isunknown(word) && word == exp_data(select,row)[19-col]);
  endproperty
  assert property (word_matches_expected)
    else $error("word: mismatch exp=%b bit[%0d]=%0d, got word=%0d",
                exp_data(select,row), 19-col, exp_data(select,row)[19-col], word);

  // When mapping is undefined (sel==2'b10 or out-of-range row), word must be X/Z
  property x_when_undefined;
    (exp_data(select,row) === 20'hx) |-> $isunknown(word);
  endproperty
  assert property (x_when_undefined)
    else $error("word: expected X/Z when undefined (sel=%b,row=%0d), got %0d", select, row, word);

  // If col is out of range, word must be X/Z
  property x_when_bad_col;
    (col > 5'd19) |-> $isunknown(word);
  endproperty
  assert property (x_when_bad_col)
    else $error("word: expected X/Z when col out of range: col=%0d", col);

  // Coverage

  // Select values exercised
  cover property (select == 2'b00);
  cover property (select == 2'b01);
  cover property (select == 2'b10);
  cover property (select == 2'b11);

  // Rows 0..19 exercised for defined selects
  genvar r;
  generate
    for (r = 0; r < 20; r++) begin : ROW_COV
      cover property (select == 2'b00 && row == r);
      cover property (select == 2'b01 && row == r);
      cover property (select == 2'b11 && row == r);
    end
  endgenerate

  // Column boundary coverage (valid range)
  cover property (col == 5'd0);
  cover property (col == 5'd19);

  // Observe both 0 and 1 outputs under defined mapping
  cover property (exp_data(select,row) !== 20'hx && col <= 5'd19 && word == 1'b0);
  cover property (exp_data(select,row) !== 20'hx && col <= 5'd19 && word == 1'b1);

endmodule

// Bind into the DUT
bind word word_sva u_word_sva (.row(row), .col(col), .select(select), .word(word));