// SVA for CAR_CTR
module CAR_CTR_sva (
  input  logic clk,
  input  logic reset_n,
  input  logic infL,
  input  logic infR,
  input  logic md1,
  input  logic md2,
  input  logic md3,
  input  logic md4
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Sanity: inputs/outputs known
  a_inputs_known:  assert property (!$isunknown({infL,infR}));
  a_outputs_known: assert property (!$isunknown({md1,md2,md3,md4}));

  // Functional equivalence (combinational spec)
  a_md1_func: assert property (md1 == ~infL);
  a_md3_func: assert property (md3 == ~infR);
  a_md2_low:  assert property (md2 == 1'b0);
  a_md4_low:  assert property (md4 == 1'b0);

  // Change-causality (each output only depends on its sensor)
  a_md1_change_cause: assert property ($changed(md1) |-> $changed(infL));
  a_md3_change_cause: assert property ($changed(md3) |-> $changed(infR));

  // Functional mapping coverage (all 4 behaviors)
  c_fwd:  cover property (infL==1'b0 && infR==1'b0 && md1 && md3 && !md2 && !md4);
  c_rgt:  cover property (infL==1'b1 && infR==1'b0 && !md1 && md3 && !md2 && !md4);
  c_lft:  cover property (infL==1'b0 && infR==1'b1 && md1 && !md3 && !md2 && !md4);
  c_stop: cover property (infL==1'b1 && infR==1'b1 && !md1 && !md3 && !md2 && !md4);

  // Transition coverage between behaviors (optional but concise)
  c_any_to_any: cover property (##1 1); // ensure multiple samples for transition analysis
  c_fwd_to_stop:  cover property ((infL==0 && infR==0) ##1 (infL==1 && infR==1));
  c_stop_to_fwd:  cover property ((infL==1 && infR==1) ##1 (infL==0 && infR==0));
  c_lft_to_rgt:   cover property ((infL==0 && infR==1) ##1 (infL==1 && infR==0));
  c_rgt_to_lft:   cover property ((infL==1 && infR==0) ##1 (infL==0 && infR==1));

endmodule

// Bind into DUT
bind CAR_CTR CAR_CTR_sva u_car_ctr_sva (
  .clk     (clk),
  .reset_n (reset_n),
  .infL    (infL),
  .infR    (infR),
  .md1     (md1),
  .md2     (md2),
  .md3     (md3),
  .md4     (md4)
);