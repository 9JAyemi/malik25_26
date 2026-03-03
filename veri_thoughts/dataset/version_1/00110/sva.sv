// SVA checker for four_to_one_circuit
module four_to_one_circuit_sva (
  input logic X,
  input logic A1, A2, B1, B2,
  input logic VPWR, VGND, VPB, VNB
);

  // Power/body status and functional terms
  wire power_ok     = (VPWR === 1'b1) && (VGND === 1'b0);
  wire body_ok      = (VPB  === 1'b1) && (VNB  === 1'b0);
  wire inputs_known = !$isunknown({A1,A2,B1,B2});

  wire and1 = (~A1) & (~A2) & (~B1) & ( B2);
  wire and2 = ( A1) & ( A2) & (~B1) & (~B2);
  wire x_exp = ~(and1 | and2);

  // Disable all checks when power rails are not good
  default disable iff (!power_ok);

  // Body-bias must match rails when power is good
  assert property (@(VPWR or VGND or VPB or VNB) power_ok |-> body_ok)
    else $error("Body-bias pins not tied correctly to rails");

  // Functional equivalence (and X must be 0/1) when inputs are known
  assert property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB)
                   inputs_known |-> (X === x_exp))
    else $error("X does not match boolean spec");

  // Mutually exclusive minterms
  assert property (@(A1 or A2 or B1 or B2) !(and1 && and2))
    else $error("Minterms and1 and and2 are not mutually exclusive");

  // Strong corollary: B1 high forces X high (both minterms require ~B1)
  assert property (@(B1 or A1 or A2 or B2) inputs_known && (B1===1'b1) |-> (X===1'b1))
    else $error("B1=1 should force X=1");

  // Coverage: exercise key functional corners
  cover property (@(A1 or A2 or B1 or B2) inputs_known && and1 && (X===1'b0));
  cover property (@(A1 or A2 or B1 or B2) inputs_known && and2 && (X===1'b0));
  cover property (@(A1 or A2 or B1 or B2) inputs_known && (X===1'b0));
  cover property (@(A1 or A2 or B1 or B2) inputs_known && (X===1'b1));

endmodule

// Bind SVA to DUT
bind four_to_one_circuit four_to_one_circuit_sva sva_inst (
  .X(X), .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);