// SVA checker for mult_16bit_signed
module mult_16bit_signed_sva (
  input  logic                clk,
  input  logic                rst_n,
  input  logic signed [15:0]  M,
  input  logic signed [15:0]  N,
  input  logic signed [31:0]  P
);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness (combinational, zero-latency)
  a_func_correct: assert property (disable iff (!rst_n)
    P == $signed(M) * $signed(N)
  );

  // No-X on output when inputs are known
  a_no_x: assert property (disable iff (!rst_n)
    !$isunknown({M,N}) |-> !$isunknown(P)
  );

  // Stability: if inputs hold, output holds
  a_hold_when_inputs_hold: assert property (disable iff (!rst_n)
    $stable({M,N}) |-> $stable(P)
  );

  // Basic algebraic identities (redundant with main check but good sanity)
  a_zero_mul_M: assert property (disable iff (!rst_n)
    (M == 0) |-> (P == 0)
  );
  a_zero_mul_N: assert property (disable iff (!rst_n)
    (N == 0) |-> (P == 0)
  );
  a_one_mul_M: assert property (disable iff (!rst_n)
    (M == 16'sd1) |-> (P == $signed(N))
  );
  a_one_mul_N: assert property (disable iff (!rst_n)
    (N == 16'sd1) |-> (P == $signed(M))
  );
  a_neg_one_mul_M: assert property (disable iff (!rst_n)
    (M == -16'sd1) |-> (P == -$signed(N))
  );
  a_neg_one_mul_N: assert property (disable iff (!rst_n)
    (N == -16'sd1) |-> (P == -$signed(M))
  );

  // Coverage: sign combinations and edge values
  cover_pos_pos:  cover property (disable iff (!rst_n)
    (M > 0 && N > 0 && P > 0));
  cover_neg_neg:  cover property (disable iff (!rst_n)
    (M < 0 && N < 0 && P > 0));
  cover_pos_neg:  cover property (disable iff (!rst_n)
    ((M > 0 && N < 0) || (M < 0 && N > 0)) && (P < 0));
  cover_zero_any: cover property (disable iff (!rst_n)
    (M == 0 || N == 0) && (P == 0));

  // Boundary covers
  cover_max_max:  cover property (disable iff (!rst_n)
    (M == 16'sh7fff && N == 16'sh7fff && P == $signed(16'sh7fff) * $signed(16'sh7fff)));
  cover_min_min:  cover property (disable iff (!rst_n)
    (M == 16'sh8000 && N == 16'sh8000 && P == $signed(16'sh8000) * $signed(16'sh8000)));
  cover_min_neg1: cover property (disable iff (!rst_n)
    (M == 16'sh8000 && N == -16'sd1 && P == $signed(16'sh8000) * -16'sd1));
  cover_max_neg1: cover property (disable iff (!rst_n)
    (M == 16'sh7fff && N == -16'sd1 && P == -$signed(16'sh7fff)));

endmodule

// Bind example (instantiate a clock/reset in TB and bind)
bind mult_16bit_signed mult_16bit_signed_sva
  u_mult_16bit_signed_sva (
    .clk  (clk),
    .rst_n(rst_n),
    .M    (M),
    .N    (N),
    .P    (P)
  );