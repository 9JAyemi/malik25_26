// SVA checkers and binds for binary_adder and full_adder

module binary_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       carry_in,
  input  logic [3:0] S,
  input  logic       carry_out,
  // internal nets bound hierarchically
  input  logic [3:0] sum,
  input  logic       c0,
  input  logic       c1,
  input  logic       c2
);
  // Basic functional equivalence and X-prop
  assert property (@(*) !$isunknown({A,B,carry_in}) |-> !$isunknown({S,carry_out,sum,c0,c1,c2}));
  assert property (@(*) !$isunknown({A,B,carry_in}) |-> {carry_out,S} == A + B + carry_in);

  // S equals internal sum
  assert property (@(*) S == sum);

  // Bit-level sum correctness vs local carry-in
  logic [3:0] cin;
  assign cin = {c2, c1, c0, carry_in}; // cin[0]=carry_in, cin[1]=c0, cin[2]=c1, cin[3]=c2

  genvar i;
  generate
    for (i=0; i<4; i++) begin : g_sum_bit
      assert property (@(*) !$isunknown({A[i],B[i],cin[i]}) |-> sum[i] == (A[i] ^ B[i]) ^ cin[i]);
    end
  endgenerate

  // Ripple carry equations
  assert property (@(*) !$isunknown({A[0],B[0],carry_in}) |-> c0 == (A[0] & B[0]) | ((A[0]^B[0]) & carry_in));
  assert property (@(*) !$isunknown({A[1],B[1],c0     }) |-> c1 == (A[1] & B[1]) | ((A[1]^B[1]) & c0     ));
  assert property (@(*) !$isunknown({A[2],B[2],c1     }) |-> c2 == (A[2] & B[2]) | ((A[2]^B[2]) & c1     ));
  assert property (@(*) !$isunknown({A[3],B[3],c2     }) |-> carry_out == (A[3] & B[3]) | ((A[3]^B[3]) & c2));

  // Concise but meaningful coverage
  // Final carry 0/1
  cover property (@(*) carry_out == 0);
  cover property (@(*) carry_out == 1);

  // Sum extremes
  cover property (@(*) S == 4'h0 && carry_out == 0);
  cover property (@(*) S == 4'hF);

  // Ripple-through case: all propagate and incoming carry generates final carry
  cover property (@(*) (&(A ^ B)) && carry_in && carry_out);

  // Per-bit generate / propagate / kill observed at least once
  cover property (@(*) (A[0] & B[0])); cover property (@(*) (A[1] & B[1]));
  cover property (@(*) (A[2] & B[2])); cover property (@(*) (A[3] & B[3]));
  cover property (@(*) (A[0] ^ B[0])); cover property (@(*) (A[1] ^ B[1]));
  cover property (@(*) (A[2] ^ B[2])); cover property (@(*) (A[3] ^ B[3]));
  cover property (@(*) (~A[0] & ~B[0])); cover property (@(*) (~A[1] & ~B[1]));
  cover property (@(*) (~A[2] & ~B[2])); cover property (@(*) (~A[3] & ~B[3]));
endmodule

module full_adder_sva (
  input logic a,
  input logic b,
  input logic carry_in,
  input logic sum,
  input logic carry_out
);
  // Functional correctness and X-prop
  assert property (@(*) !$isunknown({a,b,carry_in}) |-> {carry_out,sum} == a + b + carry_in);
  assert property (@(*) !$isunknown({a,b,carry_in}) |-> !$isunknown({sum,carry_out}));

  // Basic coverage of modes
  cover property (@(*) (a ^ b));   // propagate
  cover property (@(*) (a & b));   // generate
  cover property (@(*) (~a & ~b)); // kill
  cover property (@(*) sum);
  cover property (@(*) carry_out);
endmodule

// Binds
bind binary_adder binary_adder_sva u_bin_add_sva (
  .A(A), .B(B), .carry_in(carry_in), .S(S), .carry_out(carry_out),
  .sum(sum), .c0(carry[0]), .c1(carry[1]), .c2(carry[2])
);

bind full_adder full_adder_sva u_full_add_sva (.*);