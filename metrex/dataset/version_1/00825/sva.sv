// SVA checker for var13_multi (combinational)
// Bind this module to the DUT to validate arithmetic and the valid output.
// Focuses on correctness, boundary behavior, X-prop, and basic coverage.

module var13_multi_sva (
  input logic A, B, C, D, E, F, G, H, I, J, K, L, M,
  input logic valid
);
  localparam logic [7:0] MIN_VALUE  = 8'd121;
  localparam logic [7:0] MAX_WEIGHT = 8'd60;
  localparam logic [7:0] MAX_VOLUME = 8'd60;

  logic [7:0] exp_total_value;
  logic [7:0] exp_total_weight;
  logic [7:0] exp_total_volume;
  logic       exp_valid;

  always_comb begin
    // Recompute with identical 8-bit truncation semantics as DUT
    exp_total_value =
          A * 8'd4
        + B * 8'd8
        + C * 8'd0
        + D * 8'd20
        + E * 8'd10
        + F * 8'd12
        + G * 8'd18
        + H * 8'd14
        + I * 8'd6
        + J * 8'd15
        + K * 8'd30
        + L * 8'd8
        + M * 8'd16;

    exp_total_weight =
          A * 8'd28
        + B * 8'd8
        + C * 8'd27
        + D * 8'd18
        + E * 8'd27
        + F * 8'd28
        + G * 8'd6
        + H * 8'd1
        + I * 8'd20
        + J * 8'd0
        + K * 8'd5
        + L * 8'd13
        + M * 8'd8;

    exp_total_volume =
          A * 8'd27
        + B * 8'd27
        + C * 8'd4
        + D * 8'd4
        + E * 8'd0
        + F * 8'd24
        + G * 8'd4
        + H * 8'd20
        + I * 8'd12
        + J * 8'd15
        + K * 8'd5
        + L * 8'd2
        + M * 8'd9;

    exp_valid = (exp_total_value >= MIN_VALUE)
              && (exp_total_weight <= MAX_WEIGHT)
              && (exp_total_volume <= MAX_VOLUME);

    // Assertions
    assert (!$isunknown({A,B,C,D,E,F,G,H,I,J,K,L,M,valid}))
      else $error("var13_multi: X/Z detected on inputs or valid");

    assert (valid === exp_valid)
      else $error("var13_multi: valid mismatch (exp=%0b)", exp_valid);

    // Sanity/boundary covers
    cover (valid);
    cover (!valid);

    cover (exp_total_value == MIN_VALUE);
    cover (exp_total_weight == MAX_WEIGHT);
    cover (exp_total_volume == MAX_VOLUME);

    cover (exp_total_value == MIN_VALUE
        && exp_total_weight <= MAX_WEIGHT
        && exp_total_volume <= MAX_VOLUME); // boundary accept

    // Per-input activity coverage
    cover (A); cover (B); cover (C); cover (D); cover (E); cover (F);
    cover (G); cover (H); cover (I); cover (J); cover (K); cover (L); cover (M);

    // Trivial reject corner: all-zero selection must be invalid
    if (~|{A,B,C,D,E,F,G,H,I,J,K,L,M}) assert (!valid);
  end
endmodule

// Bind into the DUT
bind var13_multi var13_multi_sva u_var13_multi_sva (
  .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G),
  .H(H), .I(I), .J(J), .K(K), .L(L), .M(M),
  .valid(valid)
);