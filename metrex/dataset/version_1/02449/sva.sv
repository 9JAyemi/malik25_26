// SVA for FA_106 — concise, full functional checks and coverage
module FA_106_sva(input logic A, B, Ci, S, Co);
  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge Ci or negedge Ci
  ); endclocking

  // Helper: inputs are known (no X/Z)
  property inputs_known; !$isunknown({A,B,Ci}); endproperty

  // Functional correctness (full-adder spec)
  assert property (inputs_known |-> S  == (A ^ B ^ Ci))
    else $error("FA_106 S mismatch: exp=%0b got=%0b", (A^B^Ci), S);

  assert property (inputs_known |-> Co == ((A & B) | (A & Ci) | (B & Ci)))
    else $error("FA_106 Co mismatch: exp=%0b got=%0b", ((A&B)|(A&Ci)|(B&Ci)), Co);

  // Structural sanity of internal nets
  assert property (inputs_known |-> n11 == ~(A ^ B));
  assert property (inputs_known |-> S   == ~(Ci ^ n11));
  assert property (inputs_known |-> n10 == ~(A & B & Ci));
  assert property (inputs_known |-> n9  == ~(A & B));
  assert property (inputs_known |-> Co  == ~(n10 & n9));

  // Outputs must be known when inputs are known
  assert property (inputs_known |-> !$isunknown({S,Co}));

  // Truth-table stimulus coverage (all 8 input combos)
  cover property (A==0 && B==0 && Ci==0);
  cover property (A==0 && B==0 && Ci==1);
  cover property (A==0 && B==1 && Ci==0);
  cover property (A==0 && B==1 && Ci==1);
  cover property (A==1 && B==0 && Ci==0);
  cover property (A==1 && B==0 && Ci==1);
  cover property (A==1 && B==1 && Ci==0);
  cover property (A==1 && B==1 && Ci==1);

  // Behavioral coverage: propagate/generate/kill scenarios
  cover property ((A ^ B) && $changed(Ci)); // propagate (P=1) with Ci toggle
  cover property (A & B);                   // generate (G=1)
  cover property (!(A | B));                // kill (K=1)

  // Output coverage
  cover property (S==1);
  cover property (Co==1);
endmodule

bind FA_106 FA_106_sva fa_106_sva_i(.*);