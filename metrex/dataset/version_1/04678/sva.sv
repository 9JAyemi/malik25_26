// SVA for barrel_shifter
// Concise, high-quality checks and coverage. Bind this file to the DUT.

module barrel_shifter_sva (
  input logic        clk,
  input logic [15:0] A,
  input logic [3:0]  B,
  input logic        S,
  input logic [15:0] P
);

  // simple past-valid to avoid $past() at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  function automatic logic [15:0] rol16 (input logic [15:0] a, input logic [3:0] b);
    // rotate-left by b (b in 0..15)
    rol16 = (a << b) | (a >> (16 - b));
  endfunction

  // Inputs/outputs must be known at sampling (no X/Z)
  a_inputs_known:  assert property (@(posedge clk) disable iff (!past_valid)
                                    !$isunknown({A,B,S}));
  a_output_known:  assert property (@(posedge clk) disable iff (!past_valid)
                                    ##0 !$isunknown(P));

  // Golden functional check: same-cycle output equals function of previous-cycle inputs
  a_func: assert property (@(posedge clk) disable iff (!past_valid)
                           ##0 P == ( $past(S) ? rol16($past(A), $past(B))
                                              : ($past(A) << $past(B)) ));

  // Zero shift (B==0) is passthrough, both modes
  a_zero_shift: assert property (@(posedge clk) disable iff (!past_valid)
                                 ($past(B)==0) |-> ##0 (P == $past(A)));

  // Rotate preserves popcount
  a_rotate_popcount: assert property (@(posedge clk) disable iff (!past_valid)
                                      $past(S) |-> ##0 ($countones(P) == $countones($past(A))));

  // Basic mode/amount coverage
  c_s0_b0:  cover property (@(posedge clk) disable iff (!past_valid) !$past(S) && ($past(B)==0)  ##0 1);
  c_s0_b1:  cover property (@(posedge clk) disable iff (!past_valid) !$past(S) && ($past(B)==1)  ##0 1);
  c_s0_b15: cover property (@(posedge clk) disable iff (!past_valid) !$past(S) && ($past(B)==15) ##0 1);
  c_s1_b0:  cover property (@(posedge clk) disable iff (!past_valid)  $past(S) && ($past(B)==0)  ##0 1);
  c_s1_b1:  cover property (@(posedge clk) disable iff (!past_valid)  $past(S) && ($past(B)==1)  ##0 1);
  c_s1_b15: cover property (@(posedge clk) disable iff (!past_valid)  $past(S) && ($past(B)==15) ##0 1);

  // Coverage: rotation wraps MSB into LSB-side when B>0
  c_wrap: cover property (@(posedge clk) disable iff (!past_valid)
                          $past(S) && ($past(B)>0) && $past(A[15]) ##0 P[$past(B)-1]);

endmodule

bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (.*);