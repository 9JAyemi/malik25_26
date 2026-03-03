// SVA for sky130_fd_sc_ls__a211oi
// Function: Y = ~((A1 & A2) | B1 | C1)

bind sky130_fd_sc_ls__a211oi sky130_fd_sc_ls__a211oi_sva();

module sky130_fd_sc_ls__a211oi_sva;

  // Functional equivalence (4-state accurate)
  assert property (@(A1 or A2 or B1 or C1 or Y)
    Y === ~((A1 & A2) | B1 | C1));

  // Internal gate consistency
  assert property (@(A1 or A2)                     and0_out   === (A1 & A2));
  assert property (@(A1 or A2 or B1 or C1)         nor0_out_Y === ~(and0_out | B1 | C1));
  assert property (@(nor0_out_Y or Y)              Y          === nor0_out_Y);

  // Controlling values drive low
  assert property (@(B1 or A1 or A2 or C1) (B1 === 1'b1)                     |-> (Y === 1'b0));
  assert property (@(C1 or A1 or A2 or B1) (C1 === 1'b1)                     |-> (Y === 1'b0));
  assert property (@(A1 or A2 or B1 or C1) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === 1'b0));

  // Y==1 necessary/sufficient conditions
  assert property (@(A1 or A2 or B1 or C1 or Y)
    (Y === 1'b1) |-> (B1 === 1'b0 && C1 === 1'b0 && !(A1 === 1'b1 && A2 === 1'b1)));
  assert property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b0 && C1 === 1'b0 && (A1 !== 1'bx) && (A2 !== 1'bx) && !(A1 === 1'b1 && A2 === 1'b1))
      |-> (Y === 1'b1));

  // No X on Y when inputs are all known
  assert property (@(A1 or A2 or B1 or C1 or Y)
    (!$isunknown({A1,A2,B1,C1})) |-> !$isunknown(Y));

  // Power/ground rails constant
  assert property (@(VPWR or VGND or VPB or VNB)
    (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0));

  // Coverage: output toggles
  cover property (@(A1 or A2 or B1 or C1 or Y) $rose(Y));
  cover property (@(A1 or A2 or B1 or C1 or Y) $fell(Y));

  // Coverage: key functional scenarios
  cover property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b1 && C1 === 1'b0 && A1 !== 1'bx && A2 !== 1'bx && Y === 1'b0));
  cover property (@(A1 or A2 or B1 or C1 or Y)
    (C1 === 1'b1 && B1 === 1'b0 && A1 !== 1'bx && A2 !== 1'bx && Y === 1'b0));
  cover property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b1 && A2 === 1'b1 && Y === 1'b0));

  cover property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b0 && A2 === 1'b0 && Y === 1'b1));
  cover property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b1 && A2 === 1'b0 && Y === 1'b1));
  cover property (@(A1 or A2 or B1 or C1 or Y)
    (B1 === 1'b0 && C1 === 1'b0 && A1 === 1'b0 && A2 === 1'b1 && Y === 1'b1));

  // Optional: observe X propagation on Y
  cover property (@(A1 or A2 or B1 or C1 or Y) $isunknown(Y));

endmodule