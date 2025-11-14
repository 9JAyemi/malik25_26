// SVA for digital_circuit_module
// Bindable, concise, and focused on functional correctness and key pins

module digital_circuit_module_sva (
  input logic A1, A2, B1_N,
  input logic VPWR, VGND, VPB, VNB,
  input logic Y
);

  // Combinational sampling event on any relevant signal change
  event comb_ev;
  always @(A1 or A2 or B1_N or VPWR or VGND or VPB or VNB or Y) -> comb_ev;

  // Functional correctness (power on)
  assert property (@(comb_ev)
    (VPWR === 1'b1 && !$isunknown({A1,A2,B1_N})) |-> (Y === (A1 & A2 & B1_N))
  ) else $error("Y must equal A1&A2&B1_N when VPWR=1");

  // Functional correctness (power off)
  assert property (@(comb_ev)
    (VPWR === 1'b0 && !$isunknown({A1,A2,B1_N})) |-> (Y === ~(A1 & A2 & B1_N))
  ) else $error("Y must equal ~(A1&A2&B1_N) when VPWR=0");

  // Known inputs imply known output
  assert property (@(comb_ev)
    (!$isunknown({A1,A2,B1_N,VPWR})) |-> !$isunknown(Y)
  ) else $error("Y unknown despite all controlling inputs known");

  // Well pin tie checks (typical cell usage)
  assert property (@(comb_ev)
    (!$isunknown({VPB,VPWR})) |-> (VPB === VPWR)
  ) else $error("VPB must tie to VPWR");

  assert property (@(comb_ev)
    (!$isunknown({VNB,VGND})) |-> (VNB === VGND)
  ) else $error("VNB must tie to VGND");

  // Ground should be 0 when known
  assert property (@(comb_ev)
    !$isunknown(VGND) |-> (VGND === 1'b0)
  ) else $error("VGND must be 0");

  // Minimal but meaningful coverage
  cover property (@(comb_ev) VPWR===1'b1 && Y===1'b1);
  cover property (@(comb_ev) VPWR===1'b1 && Y===1'b0);
  cover property (@(comb_ev) VPWR===1'b0 && Y===1'b1);
  cover property (@(comb_ev) VPWR===1'b0 && Y===1'b0);

  cover property (@(comb_ev) $changed(A1));
  cover property (@(comb_ev) $changed(A2));
  cover property (@(comb_ev) $changed(B1_N));
  cover property (@(comb_ev) $changed(VPWR));

endmodule

bind digital_circuit_module digital_circuit_module_sva sva_inst (.*);