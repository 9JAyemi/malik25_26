module multiplier_sva #(
  parameter int n = 4
) (
  input logic clk,
  input logic [n-1:0] A,
  input logic [n-1:0] B,
  input logic mode,
  input logic signed [2*n-1:0] P
);

function automatic logic signed [2*n-1:0] sign_extend(input logic [n-1:0] v);
  sign_extend = $signed(v);
endfunction

function automatic logic [2*n-1:0] zero_extend(input logic [n-1:0] v);
  zero_extend = v;
endfunction

function automatic logic signed [2*n-1:0] signed_product(input logic [n-1:0] a, input logic [n-1:0] b);
  signed_product = $signed(a) * $signed(b);
endfunction

function automatic logic [2*n-1:0] unsigned_product(input logic [n-1:0] a, input logic [n-1:0] b);
  unsigned_product = a * b;
endfunction

// In signed mode, P must equal the signed product of A and B.
check_signed_mode_product: assert property (
  @(posedge clk) (mode == 1'b1) |-> (P == signed_product(A, B))
);

// In unsigned mode, P must equal the unsigned product of A and B.
check_unsigned_mode_product: assert property (
  @(posedge clk) (mode == 1'b0) |-> (P == unsigned_product(A, B))
);

// With unchanged inputs and mode, the sampled output must remain unchanged.
check_stable_inputs_hold_output: assert property (
  @(posedge clk) $stable(A) && $stable(B) && $stable(mode) |-> $stable(P)
);

// A rising mode selects the signed multiplication result.
check_mode_switch_to_signed: assert property (
  @(posedge clk) $rose(mode) && $stable(A) && $stable(B) |-> (P == signed_product(A, B))
);

// A falling mode selects the unsigned multiplication result.
check_mode_switch_to_unsigned: assert property (
  @(posedge clk) $fell(mode) && $stable(A) && $stable(B) |-> (P == unsigned_product(A, B))
);

// In signed mode, any zero operand must force a zero product.
check_signed_zero_operand: assert property (
  @(posedge clk) (mode == 1'b1) && ((A == '0) || (B == '0)) |-> (P == '0)
);

// In unsigned mode, any zero operand must force a zero product.
check_unsigned_zero_operand: assert property (
  @(posedge clk) (mode == 1'b0) && ((A == '0) || (B == '0)) |-> (P == '0)
);

// In signed mode, non-negative inputs must match the unsigned product.
check_signed_non_negative_matches_unsigned: assert property (
  @(posedge clk) (mode == 1'b1) && (A[n-1] == 1'b0) && (B[n-1] == 1'b0) |-> (P == unsigned_product(A, B))
);

// In signed mode, multiplying by -1 on A must negate the sign-extended B.
check_signed_a_is_minus_one: assert property (
  @(posedge clk) (mode == 1'b1) && (A == {n{1'b1}}) |-> (P == -sign_extend(B))
);

// In unsigned mode, multiplying by 1 on A must pass through B with zero extension.
check_unsigned_a_is_one: assert property (
  @(posedge clk) (mode == 1'b0) && (A == {{(n-1){1'b0}}, 1'b1}) |-> (P == zero_extend(B))
);

endmodule