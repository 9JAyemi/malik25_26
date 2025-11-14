// SVA for shift_add/shift_register/adder
// Quality-focused, concise, with key functional checks and targeted coverage

// Checker for top-level shift_add
module shift_add_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Inputs known
  assert property (!$isunknown({reset, shift_dir, data_in}));

  // Synchronous reset behavior of top shift_reg
  assert property (reset |=> shift_reg == 8'h00);

  // shift_reg capture: zero-extend MSBs, bit[4]=shift_dir, [3:0]=adder_out
  assert property (1'b1 |=> (shift_reg[7:5] == 3'b000
                             && shift_reg[4] == $past(shift_dir)
                             && shift_reg[3:0] == $past(adder_out)));

  // Adder wiring and module output wiring
  assert property (data_out == shift_reg_out);
  assert property (adder_out == ((shift_reg_out + data_in) & 4'hF));

  // Targeted coverage
  cover property (reset ##1 !reset);                          // reset deassert
  cover property (!reset && shift_dir ##1 !reset && !shift_dir); // both directions seen
  cover property (((shift_reg_out + data_in) > 4'hF));        // adder carry/overflow
endmodule

// Checker for shift_register
module shift_register_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Inputs known
  assert property (!$isunknown({reset, shift_dir, data_in}));

  // Synchronous reset behavior
  assert property (reset |=> shift_reg == 8'h00);

  // Next-state functional checks (reflecting actual coded truncation behavior)
  // shift_dir=1: left shift by 4 nibble with data_in loaded into low nibble
  assert property (shift_dir |=> shift_reg == { $past(shift_reg[3:0]), $past(data_in) });
  // shift_dir=0: effectively left shift by 1 with MSB <= data_in[0]
  assert property (!shift_dir |=> shift_reg == { $past(data_in[0]), $past(shift_reg[7:1]) });

  // Output mapping (sampled safely one cycle later)
  assert property (data_out == $past(shift_reg[3:0]));

  // Coverage: exercise both directions
  cover property (shift_dir);
  cover property (!shift_dir);
endmodule

// Checker for adder
module adder_sva;
  // Combinational correctness and X checks on any change
  assert property (@(a or b or sum) sum == ((a + b) & 4'hF));
  assert property (@(a or b or sum) !$isunknown({a, b, sum}));

  // Coverage: carry-out condition
  cover property (@(a or b) ((a + b) > 4'hF));
endmodule

// Bind checkers
bind shift_add       shift_add_sva   shift_add_sva_i();
bind shift_register  shift_register_sva shift_register_sva_i();
bind adder           adder_sva       adder_sva_i();