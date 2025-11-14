// SVA for nor3_module
// Bind these assertions to the DUT

`ifndef NOR3_MODULE_SVA
`define NOR3_MODULE_SVA

module nor3_module_sva (
  input logic A,
  input logic B,
  input logic C_N,
  input logic Y,
  input logic VPWR,
  input logic VGND
);

  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C_N or negedge C_N or
    posedge Y or negedge Y
  ); endclocking

  // Power rails
  ap_vpwr_const: assert property (VPWR === 1'b1);
  ap_vgnd_const: assert property (VGND === 1'b0);

  // Functional correctness (4-state exact)
  ap_func_4state: assert property (Y === ~(A | B | C_N));

  // Strengthened special cases
  ap_any1_low:   assert property ((A===1 || B===1 || C_N===1) |=> (Y===1'b0));
  ap_all0_high:  assert property ((A===0 && B===0 && C_N===0) |=> (Y===1'b1));

  // No X on output when inputs are all known
  ap_known_out_when_known_in: assert property ((!$isunknown({A,B,C_N})) |=> (!$isunknown(Y)));

  // Truth-table coverage (only when inputs/outputs are known)
  cover property (A===0 && B===0 && C_N===0 && Y===1);
  cover property (A===0 && B===0 && C_N===1 && Y===0);
  cover property (A===0 && B===1 && C_N===0 && Y===0);
  cover property (A===0 && B===1 && C_N===1 && Y===0);
  cover property (A===1 && B===0 && C_N===0 && Y===0);
  cover property (A===1 && B===0 && C_N===1 && Y===0);
  cover property (A===1 && B===1 && C_N===0 && Y===0);
  cover property (A===1 && B===1 && C_N===1 && Y===0);

  // Output toggle coverage
  cover property ($rose(Y));
  cover property ($fell(Y));

endmodule

bind nor3_module nor3_module_sva sva_i (.*);

`endif