// SVA for xor_gate
// Quality-focused, concise checks + coverage. Bind to DUT.

`ifndef XOR_GATE_SVA
`define XOR_GATE_SVA

module xor_gate_sva (
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic XOR_output
);

  // Power-good and known-input helpers
  wire pgood    = (VPWR === 1'b1) && (VGND === 1'b0);
  wire in_known = !($isunknown(VPB) || $isunknown(VNB));

  // Event-based sampling on input activity
  default clocking cb @(posedge VPB or negedge VPB or posedge VNB or negedge VNB); endclocking

  // Functional correctness when powered and inputs known
  property p_func_known;
    (pgood && in_known) |-> ##0 (XOR_output === (VPB ^ VNB));
  endproperty
  assert property (p_func_known)
    else $error("xor_gate: XOR_output != VPB ^ VNB with known inputs and power-good");

  // Output is known when inputs are known (no X/Z leakage)
  property p_no_x_on_known;
    (pgood && in_known) |-> ##0 !$isunknown(XOR_output);
  endproperty
  assert property (p_no_x_on_known)
    else $error("xor_gate: XOR_output is X/Z with known inputs");

  // Unknown propagation: if any input is X/Z, output must be X
  property p_x_propagation;
    (pgood && ($isunknown(VPB) || $isunknown(VNB))) |-> ##0 $isunknown(XOR_output);
  endproperty
  assert property (p_x_propagation)
    else $error("xor_gate: unknown on input(s) must propagate to XOR_output");

  // Single-input toggle must toggle the XOR output
  property p_toggle_vpb;
    (pgood && in_known && $changed(VPB) && $stable(VNB)) |-> ##0 $changed(XOR_output);
  endproperty
  assert property (p_toggle_vpb)
    else $error("xor_gate: VPB toggle with VNB stable must toggle XOR_output");

  property p_toggle_vnb;
    (pgood && in_known && $changed(VNB) && $stable(VPB)) |-> ##0 $changed(XOR_output);
  endproperty
  assert property (p_toggle_vnb)
    else $error("xor_gate: VNB toggle with VPB stable must toggle XOR_output");

  // Functional coverage (all input combinations with expected output)
  cover property (pgood && VPB === 1'b0 && VNB === 1'b0 && XOR_output === 1'b0);
  cover property (pgood && VPB === 1'b0 && VNB === 1'b1 && XOR_output === 1'b1);
  cover property (pgood && VPB === 1'b1 && VNB === 1'b0 && XOR_output === 1'b1);
  cover property (pgood && VPB === 1'b1 && VNB === 1'b1 && XOR_output === 1'b0);

  // Output toggle coverage
  cover property (pgood && $rose(XOR_output));
  cover property (pgood && $fell(XOR_output));

endmodule

bind xor_gate xor_gate_sva
(
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB(VPB),
  .VNB(VNB),
  .XOR_output(XOR_output)
);

`endif