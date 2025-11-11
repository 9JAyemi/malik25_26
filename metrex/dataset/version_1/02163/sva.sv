// SVA checker for full_adder
module full_adder_sva;
  // Bound inside full_adder; hierarchical names A,B,Ci,S,Co,n1,n2,n3 are visible
  default clocking cb @(*); endclocking

  // No X/Zs
  assert property (!$isunknown({A,B,Ci}));
  assert property (!$isunknown({S,Co}));
  assert property (!$isunknown({n1,n2,n3}));

  // Golden full-adder functionality (black-box)
  assert property (S  == (A ^ B ^ Ci));
  assert property (Co == ((A & B) | (Ci & (A ^ B))));

  // Equivalent split (no temporal operators; purely combinational)
  assert property ( (Ci ? (S==~(A^B) && Co==(A|B))
                       : (S==(A^B)  && Co==(A&B))) );

  // White-box consistency with RTL structure
  assert property (n1 == ~(A ^ B));
  assert property (n2 == ~(n1 ^ Ci));
  assert property (n3 == ~(A  ^ Ci));
  assert property (Co == (n1 & Ci));
  assert property (S  == (n2 & n3));

  // Input-space coverage (all 8 combinations)
  cover property ({A,B,Ci} == 3'b000);
  cover property ({A,B,Ci} == 3'b001);
  cover property ({A,B,Ci} == 3'b010);
  cover property ({A,B,Ci} == 3'b011);
  cover property ({A,B,Ci} == 3'b100);
  cover property ({A,B,Ci} == 3'b101);
  cover property ({A,B,Ci} == 3'b110);
  cover property ({A,B,Ci} == 3'b111);

  // Output value coverage
  cover property (S==0);
  cover property (S==1);
  cover property (Co==0);
  cover property (Co==1);

  // Functional scenario coverage (generate/propagate/kill)
  cover property (Ci==0 && A&B);           // generate
  cover property (Ci==1 && (A^B));         // propagate
  cover property (Ci==0 && ~(A|B));        // kill
endmodule

bind full_adder full_adder_sva fa_sva();