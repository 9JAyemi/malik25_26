// SVA for add_sub_shift
// Bind to the DUT to check reset behavior, next-state functions, and ties

module add_sub_shift_asserts (
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic        C,
  input  logic        shift,
  input  logic        load,
  input  logic [3:0]  data_in,
  input  logic [15:0] Q,
  input  logic [3:0]  out,
  input  logic [15:0] sum,
  input  logic [3:0]  shift_reg,
  input  logic [3:0]  and_result
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset state
  assert property (reset |-> (sum==16'h0 && shift_reg==4'h0 && and_result==4'h0));
  assert property (reset |-> (Q==16'h0 && out==4'h0));

  // Combinational ties
  assert property (Q == sum);
  assert property (out == shift_reg);

  // Next-state for sum (add/sub) and post-reset value
  assert property ($past(reset) |-> sum==16'h0);
  assert property ((!reset && !$past(reset)) |-> sum == $past( C ? (A - B) : (A + B) ));

  // Next-state for shift_reg with load priority and post-reset value
  assert property ($past(reset) |-> shift_reg==4'h0);
  assert property ((!reset && !$past(reset)) |-> 
                   shift_reg == $past( load ? data_in
                                             : (shift ? {shift_reg[2:0],1'b0}
                                                      : shift_reg) ));

  // Next-state for and_result (AND of prior cycle sum[3:0] & out) and post-reset value
  assert property ($past(reset) |-> and_result==4'h0);
  assert property ((!reset && !$past(reset)) |-> and_result == $past( sum[3:0] & out ));

  // Load has priority over shift when both asserted
  assert property ((!reset && !$past(reset) && $past(load && shift)) |-> shift_reg == $past(data_in));

  // Simple functional covers
  cover property (reset ##1 !reset);                            // reset release
  cover property (!reset && !$past(reset) && (C==1'b0));        // add case
  cover property (!reset && !$past(reset) && (C==1'b1));        // sub case
  cover property (!reset && load);                              // load
  cover property (!reset && shift);                             // shift
  cover property (!reset && load && shift);                     // load+shift (priority)

  // Shift behavior spot-check cover: load then 4 shifts
  sequence s_load_then_shift4;
    (!reset && load) ##1 (!reset && shift)[*4];
  endsequence
  cover property (s_load_then_shift4);

endmodule

// Bind into DUT
bind add_sub_shift add_sub_shift_asserts i_add_sub_shift_asserts (
  .clk(clk),
  .reset(reset),
  .A(A),
  .B(B),
  .C(C),
  .shift(shift),
  .load(load),
  .data_in(data_in),
  .Q(Q),
  .out(out),
  .sum(sum),
  .shift_reg(shift_reg),
  .and_result(and_result)
);