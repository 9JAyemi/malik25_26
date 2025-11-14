// SVA for RIPPLE_CARRY_ADDER and FULL_ADDER
// Bind these into the DUTs

module RIPPLE_CARRY_ADDER_sva (
  input logic [3:0] wA,
  input logic [3:0] wB,
  input logic       wCi,
  input logic [3:0] wR,
  input logic       wCo,
  input logic [3:0] c
);

  // Top-level correctness
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> {wCo,wR} == wA + wB + wCi);

  // No X on outputs if inputs are 2-state
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> !$isunknown({wR,wCo,c}));

  // Bit 0 stage
  assert property (@(*) (!$isunknown({wA[0],wB[0],wCi})) |-> (
                    wR[0] == (wA[0]^wB[0]) ^ wCi &&
                    c[0]  == (wA[0]&wB[0]) | ((wA[0]^wB[0]) & wCi)));

  // Bits 1..2 stages
  genvar i;
  generate
    for (i=1; i<=2; i++) begin : gen_bits_1_2
      assert property (@(*) (!$isunknown({wA[i],wB[i],c[i-1]})) |-> (
                        wR[i] == (wA[i]^wB[i]) ^ c[i-1] &&
                        c[i]  == (wA[i]&wB[i]) | ((wA[i]^wB[i]) & c[i-1])));
    end
  endgenerate

  // Bit 3 (MSB) stage
  assert property (@(*) (!$isunknown({wA[3],wB[3],c[2]})) |-> (
                    wR[3] == (wA[3]^wB[3]) ^ c[2] &&
                    wCo   == (wA[3]&wB[3]) | ((wA[3]^wB[3]) & c[2])));

  // Functional coverage (concise but meaningful)
  cover property (@(*) wCi==0);
  cover property (@(*) wCi==1);
  cover property (@(*) wCo==0);
  cover property (@(*) wCo==1);

  // Zero vector and max overflow
  cover property (@(*) (wA==4'h0 && wB==4'h0 && wCi==0 && wR==4'h0 && wCo==0));
  cover property (@(*) (wA==4'hF && wB==4'hF && wCi==1 && wR==4'hF && wCo==1));

  // Full propagate chain ripple to Co
  cover property (@(*) (wCi && (&(wA^wB)) && ~(|(wA&wB)) && wCo));

  // MSB generate carry
  cover property (@(*) ((wA[3]&wB[3]) && wCo));

endmodule


module FULL_ADDER_sva (
  input logic wA, wB, wCi,
  input logic wR, wCo
);
  // Arithmetic equivalence
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> {wCo,wR} == wA + wB + wCi);

  // Boolean equations
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> wR == (wA^wB) ^ wCi);
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> wCo == (wA&wB) | ((wA^wB) & wCi));

  // Output 2-state when inputs 2-state
  assert property (@(*) (!$isunknown({wA,wB,wCi})) |-> !$isunknown({wR,wCo}));

  // Simple carry coverage
  cover property (@(*) wCo==0);
  cover property (@(*) wCo==1);
endmodule


// Binds
bind RIPPLE_CARRY_ADDER RIPPLE_CARRY_ADDER_sva b_rca (
  .wA(wA), .wB(wB), .wCi(wCi), .wR(wR), .wCo(wCo), .c(c)
);

bind FULL_ADDER FULL_ADDER_sva b_fa (
  .wA(wA), .wB(wB), .wCi(wCi), .wR(wR), .wCo(wCo)
);