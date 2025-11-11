// SVA for sky130_fd_sc_hdll__a32o
// Bindable, concise, and focused on functional correctness, X-prop robustness, unateness, and coverage.

module sky130_fd_sc_hdll__a32o_sva (
  input logic X,
  input logic A1, A2, A3,
  input logic B1, B2,
  input logic VPWR, VGND, VPB, VNB
);
  function automatic bit pgood;
    return (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  endfunction
  function automatic bit known_in;
    return !$isunknown({A1,A2,A3,B1,B2});
  endfunction

  wire expr = (A1 & A2 & A3) | (B1 & B2);

  // Power pins must be valid
  assert property (pgood());

  // Output is known and functionally correct when inputs are known
  assert property (pgood() && known_in |-> !$isunknown(X));
  assert property (pgood() && known_in |-> X == expr);

  // Determinate cases (robust to X’s on non-controlling inputs)
  assert property (pgood() && (B1===1 && B2===1) |-> X===1);
  assert property (pgood() && (A1===1 && A2===1 && A3===1) |-> X===1);
  assert property (pgood() &&
                   ((A1===0 || A2===0 || A3===0) && (B1===0 || B2===0)) |-> X===0);

  // Positive unateness: rising any input (others stable) must not make X fall
  assert property (@(posedge A1) disable iff (!pgood() || !$stable({A2,A3,B1,B2})) !$fell(X));
  assert property (@(posedge A2) disable iff (!pgood() || !$stable({A1,A3,B1,B2})) !$fell(X));
  assert property (@(posedge A3) disable iff (!pgood() || !$stable({A1,A2,B1,B2})) !$fell(X));
  assert property (@(posedge B1) disable iff (!pgood() || !$stable({A1,A2,A3,B2})) !$fell(X));
  assert property (@(posedge B2) disable iff (!pgood() || !$stable({A1,A2,A3,B1})) !$fell(X));

  // Functional coverage: each OR term alone, both, and neither; and X edges
  cover property (pgood() && (A1 && A2 && A3) && !(B1 && B2));
  cover property (pgood() && (B1 && B2) && !(A1 && A2 && A3));
  cover property (pgood() && (A1 && A2 && A3) && (B1 && B2));
  cover property (pgood() && ((A1===0 || A2===0 || A3===0) && (B1===0 || B2===0)));
  cover property (@(posedge X) pgood());
  cover property (@(negedge X) pgood());
endmodule

bind sky130_fd_sc_hdll__a32o sky130_fd_sc_hdll__a32o_sva sva_i (
  .X(X), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);