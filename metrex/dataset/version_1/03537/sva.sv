// SVA for full_adder and four_bit_adder
// Bind into DUT; no DUT modifications required

// Assertions and coverage for 1-bit full adder
module full_adder_sva;
  // Correctness when inputs known, plus X-containment
  assert property (@(*)
    !$isunknown({a,b,cin}) |->
      ({cout,sum} == ({1'b0,a} + {1'b0,b} + cin) && !$isunknown({sum,cout}))
  );
  assert property (@(*) $isunknown({sum,cout}) |-> $isunknown({a,b,cin}));

  // Exhaustive input coverage (8 combos)
  cover property (@(*) {a,b,cin} == 3'b000);
  cover property (@(*) {a,b,cin} == 3'b001);
  cover property (@(*) {a,b,cin} == 3'b010);
  cover property (@(*) {a,b,cin} == 3'b011);
  cover property (@(*) {a,b,cin} == 3'b100);
  cover property (@(*) {a,b,cin} == 3'b101);
  cover property (@(*) {a,b,cin} == 3'b110);
  cover property (@(*) {a,b,cin} == 3'b111);
endmodule

bind full_adder full_adder_sva fa_sva_i();


// Assertions and coverage for 4-bit ripple-carry adder
module four_bit_adder_sva;
  // Top-level arithmetic correctness when inputs known, plus X-containment
  assert property (@(*)
    !$isunknown({a,b,cin}) |->
      ({cout,sum} == ({1'b0,a} + {1'b0,b} + cin) && !$isunknown({sum,cout}))
  );
  assert property (@(*) $isunknown({sum,cout}) |-> $isunknown({a,b,cin}));

  // Stage-by-stage ripple correctness (also checks internal carries and wiring)
  assert property (@(*) sum[0] == (a[0] ^ b[0] ^ cin));
  assert property (@(*) c1     == ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)));
  assert property (@(*) sum[1] == (a[1] ^ b[1] ^ c1));
  assert property (@(*) c2     == ((a[1] & b[1]) | (a[1] & c1)  | (b[1] & c1)));
  assert property (@(*) sum[2] == (a[2] ^ b[2] ^ c2));
  assert property (@(*) c3     == ((a[2] & b[2]) | (a[2] & c2)  | (b[2] & c2)));
  assert property (@(*) sum[3] == (a[3] ^ b[3] ^ c3));
  assert property (@(*) cout   == c3);

  // Functional coverage of key scenarios
  // Full propagate chain with cin=1 -> cout=1
  cover property (@(*) ((a ^ b) == 4'hF) && cin && cout);
  // MSB generate -> cout=1
  cover property (@(*) (a[3] & b[3]) && cout);
  // Ripple reaches bit2 and stops before MSB
  cover property (@(*) (a[0]^b[0]) && (a[1]^b[1]) && !(a[2]^b[2]) && cin && c2 && !cout);
  // Classic full ripple case: F + 0 + 1 -> sum=0, cout=1
  cover property (@(*) (a==4'hF) && (b==4'h0) && cin && (sum==4'h0) && cout);
  // Max overflow: F + F + 1 -> sum=F, cout=1
  cover property (@(*) (a==4'hF) && (b==4'hF) && cin && (sum==4'hF) && cout);
  // See carries at each internal stage at least once
  cover property (@(*) c1);
  cover property (@(*) c2);
  cover property (@(*) c3);
endmodule

bind four_bit_adder four_bit_adder_sva four_sva_i();