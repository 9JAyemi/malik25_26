// SVA for ds8dac1: concise, high-value checks and coverage
// Bind this module to the DUT to access internals PWM_accumulator and PWM_add.

module ds8dac1_sva (
  input  logic        clk,
  input  logic [7:0]  PWM_in,
  input  logic        PWM_out,
  input  logic [8:0]  PWM_accumulator,
  input  logic [7:0]  PWM_add
);

default clocking cb_pos @(posedge clk); endclocking

// Sanity/X checks
a_in_known:    assert property (@cb_pos !$isunknown(PWM_in));
a_add_known:   assert property (@cb_pos !$isunknown(PWM_add));
a_acc_known:   assert property (@cb_pos !$isunknown(PWM_accumulator));
a_out_known:   assert property (@(negedge clk) !$isunknown(PWM_out));

// Posedge updates
// PWM_add samples PWM_in (1-cycle latency in SVA sampling)
a_add_update:  assert property (@cb_pos disable iff ($initstate)
                    PWM_add == $past(PWM_in));

// Accumulator update matches RTL (8-bit sum zero-extended to 9)
a_acc_update:  assert property (@cb_pos disable iff ($initstate)
                    PWM_accumulator == {1'b0, ($past(PWM_accumulator[7:0]) + $past(PWM_add))});

// Negedge output: PWM_out latches MSB of accumulator from the last posedge
a_out_latch:   assert property (@(negedge clk) disable iff ($initstate)
                    PWM_out == $past(PWM_accumulator[8], 0, posedge clk));

// Minimal functional coverage
c_in_nonzero:  cover  property (@cb_pos PWM_in != 8'h00);
c_in_max:      cover  property (@cb_pos PWM_in == 8'hFF);
c_acc_msb_chg: cover  property (@cb_pos $changed(PWM_accumulator[8]));
c_out_chg:     cover  property (@(negedge clk) $changed(PWM_out));

endmodule

// Example bind (put in your testbench or a separate bind file):
// bind ds8dac1 ds8dac1_sva u_ds8dac1_sva ( .clk(clk),
//                                          .PWM_in(PWM_in),
//                                          .PWM_out(PWM_out),
//                                          .PWM_accumulator(PWM_accumulator),
//                                          .PWM_add(PWM_add) );