// SVA: concise, high-quality checks and coverage for unsigned combinational multipliers

module mult_asserts #(parameter int WA=1, WB=1, WZ=WA+WB) (
  input  logic [WA-1:0] A,
  input  logic [WB-1:0] B,
  input  logic [WZ-1:0] Z
);
  localparam logic [WA-1:0] MAX_A = {WA{1'b1}};
  localparam logic [WB-1:0] MAX_B = {WB{1'b1}};
  wire has_x = $isunknown({A,B,Z});

  // Golden functional equivalence when 2-state
  assert property (@(*) disable iff (has_x) Z == ($unsigned(A) * $unsigned(B)))
    else $error("Multiplier mismatch: Z != A*B");

  // Zero/one identities
  assert property (@(*) disable iff (has_x) (A == '0) |-> (Z == '0));
  assert property (@(*) disable iff (has_x) (B == '0) |-> (Z == '0));
  assert property (@(*) disable iff (has_x) (A == {{(WA-1){1'b0}},1'b1}) |-> (Z == $unsigned(B)));
  assert property (@(*) disable iff (has_x) (B == {{(WB-1){1'b0}},1'b1}) |-> (Z == $unsigned(A)));

  // Zero result iff an operand is zero (when all are 2-state)
  assert property (@(*) disable iff (has_x) (Z == '0) |-> ((A == '0) || (B == '0)));

  // Bit-level sanity: LSB of product equals AND of operand LSBs
  assert property (@(*) disable iff (has_x) Z[0] == (A[0] & B[0]));

  // If inputs are 2-state, output must be 2-state
  assert property (@(*) (! $isunknown({A,B})) |-> (! $isunknown(Z)));

  // Corner exactness: max*max
  assert property (@(*) disable iff (has_x)
                   ((A == MAX_A) && (B == MAX_B)) |-> (Z == ($unsigned(MAX_A) * $unsigned(MAX_B))));

  // Targeted coverage (2-state only)
  cover property (@(*) !has_x && (A=='0));
  cover property (@(*) !has_x && (B=='0));
  cover property (@(*) !has_x && (A=={{(WA-1){1'b0}},1'b1}));
  cover property (@(*) !has_x && (B=={{(WB-1){1'b0}},1'b1}));
  cover property (@(*) !has_x && (A==MAX_A));
  cover property (@(*) !has_x && (B==MAX_B));
  cover property (@(*) !has_x && (A==MAX_A) && (B==MAX_B));
  cover property (@(*) !has_x && (A=='0) && (B==MAX_B));
  cover property (@(*) !has_x && (A==MAX_A) && (B=='0));
  cover property (@(*) !has_x && $onehot(A));
  cover property (@(*) !has_x && $onehot(B));
  cover property (@(*) !has_x && Z[WZ-1]); // hit top bit
endmodule

// Bind SVA to DUTs
bind mult_16x16 mult_asserts #(.WA(16), .WB(16)) u_mult_16x16_sva (.A(A), .B(B), .Z(Z));
bind mult_20x18 mult_asserts #(.WA(20), .WB(18)) u_mult_20x18_sva (.A(A), .B(B), .Z(Z));
bind mult_8x8   mult_asserts #(.WA(8),  .WB(8))  u_mult_8x8_sva   (.A(A), .B(B), .Z(Z));
bind mult_10x9  mult_asserts #(.WA(10), .WB(9))  u_mult_10x9_sva  (.A(A), .B(B), .Z(Z));