// SVA bind file for the provided design

// Dual-edge FF checks
module detff_sva (input clk, input d, input q, input _q);
  // Data captured on posedge must appear on q at following negedge
  assert property (@(negedge clk) q == $past(d, 1, posedge clk));
  // q only updates on negedge; _q only updates on posedge
  assert property (@(posedge clk) $stable(q));
  assert property (@(negedge clk) $stable(_q));
  // No X on storage nodes at clock edges
  assert property (@(posedge clk or negedge clk) !$isunknown({q,_q}));

  // Coverage
  cover property (@(posedge clk) ##1 @(negedge clk) $changed(q));
  cover property (@(negedge clk) q==1'b0);
  cover property (@(negedge clk) q==1'b1);
endmodule
bind dual_edge_triggered_ff detff_sva detff_sva_i (.clk(clk), .d(d), .q(q), ._q(_q));

// Full-adder truth and carry
module full_adder_sva (input a,b,cin,sum,cout);
  assert property (sum == (a ^ b ^ cin));
  assert property (cout == ((a & b) | (b & cin) | (cin & a)));

  // Coverage
  cover property (cout);             // carry generate case
  cover property (sum == 1'b0);      // even parity case
endmodule
bind full_adder full_adder_sva fa_sva_i (.*);

// 4-bit ripple-carry adder end-to-end sum/carry
module ripple_carry_adder_sva (input [3:0] A,B,S, input cout);
  assert property ( !$isunknown({A,B}) |-> {cout,S} == A + B );

  // Coverage: zero, max, carry out
  cover property ({cout,S} == 5'd0);
  cover property (S == 4'hF);
  cover property (cout);
endmodule
bind ripple_carry_adder ripple_carry_adder_sva rca_sva_i (.*);

// Functional XOR stage
module functional_module_sva(input [3:0] adder_output,
                             input       flip_flop_output,
                             input [3:0] final_output);
  assert property ( final_output == (adder_output ^ {4{flip_flop_output}}) );

  // Coverage: both FF polarities exercised
  cover property (flip_flop_output == 1'b0);
  cover property (flip_flop_output == 1'b1);
endmodule
bind functional_module functional_module_sva fm_sva_i (.*);

// Top-level end-to-end relation
module top_module_sva(input clk, input reset,
                      input [3:0] S,
                      input       q,
                      input [3:0] final_output);
  assert property (@(posedge clk or negedge clk) disable iff (reset)
                   final_output == (S ^ {4{q}}));

  // Coverage: both edges under non-reset
  cover property (@(posedge clk) !reset ##1 @(negedge clk) !reset);
endmodule
bind top_module top_module_sva top_sva_i (.clk(clk), .reset(reset), .S(S), .q(q), .final_output(final_output));