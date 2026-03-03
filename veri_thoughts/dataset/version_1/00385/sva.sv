// SVA for my_module: concise, structural + functional checks, with coverage.
// Bind into the DUT; no DUT edits required.

module my_module_sva (
  input Y, A1, A2, B1, B2,
  input nand0_out, nand1_out, and0_out_Y, and1_out_Y
);

  // Structural gate semantics (4-state, same-timestep sampling on any change)
  assert property (@(A1 or A2 or B1 or B2 or nand0_out or nand1_out or and0_out_Y or and1_out_Y or Y)
                   nand0_out === ~(A1 & A2));
  assert property (@(A1 or A2 or B1 or B2 or nand0_out or nand1_out or and0_out_Y or and1_out_Y or Y)
                   nand1_out === ~(B1 & B2));
  assert property (@(A1 or A2 or B1 or B2 or nand0_out or nand1_out or and0_out_Y or and1_out_Y or Y)
                   and0_out_Y === (nand0_out & nand1_out));
  assert property (@(A1 or A2 or B1 or B2 or nand0_out or nand1_out or and0_out_Y or and1_out_Y or Y)
                   and1_out_Y === ~and0_out_Y);
  assert property (@(A1 or A2 or B1 or B2 or nand0_out or nand1_out or and0_out_Y or and1_out_Y or Y)
                   Y === and1_out_Y);

  // Functional equivalence: Y == (A1&A2) | (B1&B2)
  assert property (@(A1 or A2 or B1 or B2 or Y)
                   Y === ((A1 & A2) | (B1 & B2)))
    else $error("my_module functional mismatch: Y != (A1&A2)|(B1&B2)");

  // If inputs are known (0/1), output must be known
  assert property (@(A1 or A2 or B1 or B2 or Y)
                   !$isunknown({A1,A2,B1,B2}) |-> !$isunknown(Y));

  // Functional coverage: all outcome classes
  cover property (@(A1 or A2 or B1 or B2 or Y)
                  (A1 & A2) && !(B1 & B2) ##0 (Y==1));
  cover property (@(A1 or A2 or B1 or B2 or Y)
                  !(A1 & A2) && (B1 & B2) ##0 (Y==1));
  cover property (@(A1 or A2 or B1 or B2 or Y)
                  (A1 & A2) && (B1 & B2) ##0 (Y==1));
  cover property (@(A1 or A2 or B1 or B2 or Y)
                  !(A1 & A2) && !(B1 & B2) ##0 (Y==0));

  // Output toggle coverage
  cover property (@(A1 or A2 or B1 or B2 or Y) $rose(Y));
  cover property (@(A1 or A2 or B1 or B2 or Y) $fell(Y));

endmodule

bind my_module my_module_sva sva_i (
  .Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .nand0_out(nand0_out), .nand1_out(nand1_out),
  .and0_out_Y(and0_out_Y), .and1_out_Y(and1_out_Y)
);