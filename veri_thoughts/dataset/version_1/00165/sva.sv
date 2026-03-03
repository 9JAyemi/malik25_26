// SVA for four_bit_adder (concise, high-quality checks + targeted coverage)

// Port-only checker (no internal signal dependency)
module four_bit_adder_port_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] S,
  input logic       C_out
);
  // Functional equivalence (golden reference)
  assert property (@(A or B) {C_out,S} == A + B);

  // Purely combinational: outputs only change when inputs change
  assert property (@(S or C_out) $changed({S,C_out}) |-> $changed({A,B}));

  // Known outputs when inputs are known
  assert property (@(A or B) !$isunknown({A,B}) |-> !$isunknown({S,C_out}));

  // Targeted functional coverage
  cover property (@(A or B) C_out);                // carry-out seen
  cover property (@(A or B) !C_out);               // no carry-out seen
  cover property (@(A or B) {C_out,S} == 5'd0);    // 0+0
  cover property (@(A or B) {C_out,S} == 5'd15);   // max without carry (e.g., 7+8)
  cover property (@(A or B) {C_out,S} == 5'd16);   // 15+1 ripple across all bits
  cover property (@(A or B) {C_out,S} == 5'd31);   // 15+16-? not possible; actual max 15+15=31
endmodule

// Internal chain checker (bind if internal nets available)
module four_bit_adder_chain_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [4:0] carry,
  input logic [4:0] sum
);
  // Carry-in base must be 0
  assert property (@(A or B) carry[0] == 1'b0);

  genvar i;
  generate
    for (i=0; i<4; i++) begin : bit
      // Bit-level full-adder relations
      assert property (@(A or B) sum[i]     == (A[i] ^ B[i] ^ carry[i]));
      assert property (@(A or B) carry[i+1] == ((A[i] & B[i]) | (A[i] & carry[i]) | (B[i] & carry[i])));

      // Coverage of generate / propagate / kill per bit
      cover property (@(A or B) (A[i] & B[i]) && !carry[i] && carry[i+1]);   // generate
      cover property (@(A or B) (A[i] ^ B[i]) &&  carry[i] && carry[i+1]);   // propagate 1
      cover property (@(A or B) (A[i] ^ B[i]) && !carry[i] && !carry[i+1]);  // propagate 0
      cover property (@(A or B) !(A[i] | B[i]) && !carry[i+1]);              // kill
    end
  endgenerate
endmodule

// Submodule checker for full_adder
module full_adder_sva (
  input logic A, B, C_in,
  input logic S, C_out
);
  assert property (@(A or B or C_in) {C_out,S} == A + B + C_in);
  cover  property (@(A or B or C_in) (A&B) && !C_in && C_out);    // generate
  cover  property (@(A or B or C_in) (A^B) &&  C_in && C_out);    // propagate
  cover  property (@(A or B or C_in) !(A|B) && !C_out);           // kill
endmodule

// Bind these into the DUT
bind four_bit_adder four_bit_adder_port_sva  (.A(A), .B(B), .S(S), .C_out(C_out));
bind four_bit_adder four_bit_adder_chain_sva (.A(A), .B(B), .carry(carry), .sum(sum));
bind full_adder     full_adder_sva           (.A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));