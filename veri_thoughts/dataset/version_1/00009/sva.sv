// SVA for shift_reg — concise, high-quality checks and coverage

module shift_reg_sva (
  input logic        clk,
  input logic        en,
  input logic        din,
  input logic [7:0]  dout
);

  // Track that at least one clock has occurred for $past() safety
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // X/Z checks
  a_no_x_in:  assert property (@(posedge clk) !$isunknown({en, din}));
  a_no_x_out: assert property (@(posedge clk) disable iff (!past_valid) !$isunknown(dout));

  // Functional correctness
  // Hold when en==0
  a_hold:  assert property (@(posedge clk) disable iff (!past_valid)
                            !en |-> $stable(dout));

  // Shift when en==1: new dout == {past dout[6:0], past din}
  a_shift: assert property (@(posedge clk) disable iff (!past_valid)
                            en |-> dout == { $past(dout)[6:0], $past(din) });

  // Output changes only if the previous cycle had en==1
  a_change_only_when_en: assert property (@(posedge clk) disable iff (!past_valid)
                                          $changed(dout) |-> $past(en));

  // Coverage
  // Observe at least 3 consecutive idle cycles
  c_hold:           cover property (@(posedge clk) (!en)[*3]);

  // Enable toggling activity
  c_en_toggle:      cover property (@(posedge clk) !en ##1 en ##1 !en);

  // A single '1' on din reaches MSB after 7 enabled shifts
  c_one_to_msb:     cover property (@(posedge clk) (en && din) ##1 (en)[*7] ##0 dout[7]);

  // Fully load ones/zeros via serial input over 8 enabled cycles
  c_fill_ones:      cover property (@(posedge clk) (en && din)[*8]    ##0 (dout == 8'hFF));
  c_fill_zeros:     cover property (@(posedge clk) (en && !din)[*8]   ##0 (dout == 8'h00));

endmodule

bind shift_reg shift_reg_sva sva_i (.*);