// SVA checker for shift_register
module shift_register_sva (
  input logic        clk, rst, load, shift_left, shift_right, serial_in,
  input logic [3:0]  shift_reg
);

  default clocking @(posedge clk); endclocking

  // Reset behavior (synchronous)
  assert property (rst |-> shift_reg == 4'b0000);

  // Disable other checks while in reset
  default disable iff (rst);

  // Priority-encoded next-state checks
  // load (1-bit zero-extends to 4 bits per RTL)
  assert property (load |=> shift_reg == {3'b000, $past(serial_in)});

  // shift_left (rotate left)
  assert property (!load && shift_left
                   |=> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])});

  // shift_right (as coded; note uses bit[1] into MSB)
  assert property (!load && !shift_left && shift_right
                   |=> shift_reg == {$past(shift_reg[1]), $past(shift_reg[3:1])});

  // hold (no controls)
  assert property (!load && !shift_left && !shift_right
                   |=> shift_reg == $past(shift_reg));

  // Precedence when multiple controls are high
  assert property ((load && (shift_left || shift_right))
                   |=> shift_reg == {3'b000, $past(serial_in)});
  assert property ((!load && shift_left && shift_right)
                   |=> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])});

  // Sanity: no X/Z in operational cycles
  assert property (!$isunknown(shift_reg));

  // Cover: each branch taken and key corner cases
  cover property (rst |-> shift_reg == 4'b0000);
  cover property (load |=> shift_reg == {3'b000, $past(serial_in)});
  cover property (!load && shift_left
                  |=> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])});
  cover property (!load && !shift_left && shift_right
                  |=> shift_reg == {$past(shift_reg[1]), $past(shift_reg[3:1])});
  cover property (!load && !shift_left && !shift_right
                  |=> shift_reg == $past(shift_reg));
  // Wrap-around examples
  cover property (!load && shift_left && $past(shift_reg)==4'b1000
                  |=> shift_reg==4'b0001);
  cover property (!load && !shift_left && shift_right && $past(shift_reg)==4'b0010
                  |=> shift_reg==4'b1001);
  // Precedence combos
  cover property (load && shift_left |=> shift_reg == {3'b000, $past(serial_in)});
  cover property (!load && shift_left && shift_right
                  |=> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])});

endmodule

// Bind into DUT
bind shift_register shift_register_sva sva_i (
  .clk(clk), .rst(rst), .load(load), .shift_left(shift_left),
  .shift_right(shift_right), .serial_in(serial_in), .shift_reg(shift_reg)
);