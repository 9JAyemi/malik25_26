// SVA for d_ff_sr: synchronous-reset D flip-flop (sr high -> Q=0; else Q:=D)
module d_ff_sr_sva (
  input logic clk,
  input logic D,
  input logic sr,
  input logic Q
);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness: next-cycle Q equals (sr ? 0 : D) sampled this cycle
  a_func: assert property (1'b1 |-> ##1 (Q == (sr ? 1'b0 : D)));

  // No X on inputs at sampling, and Q never X at sampled times
  a_x_in:  assert property (!$isunknown({sr, D}));
  a_x_out: assert property (!$isunknown(Q));

  // Q must not change on negedge (no unintended async behavior/glitches at negedge)
  a_no_negedge_update: assert property (@(negedge clk) $stable(Q));

  // Coverage: exercise reset path and both data values under !sr
  c_reset_path: cover property (sr ##1 (Q == 1'b0));
  c_data_1:     cover property (!sr && D    ##1 (Q == 1'b1));
  c_data_0:     cover property (!sr && !D   ##1 (Q == 1'b0));
  // Coverage: data capture toggle under !sr
  c_toggle_up:   cover property (!sr && !D ##1 (Q==0) ##1 (!sr && D) ##1 (Q==1));
  c_toggle_down: cover property (!sr &&  D ##1 (Q==1) ##1 (!sr && !D) ##1 (Q==0));

endmodule

// Bind into DUT
bind d_ff_sr d_ff_sr_sva sva_i (.clk(clk), .D(D), .sr(sr), .Q(Q));