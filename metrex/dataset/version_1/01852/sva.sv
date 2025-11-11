// SVA checker for mux4to1
module mux4to1_sva (
  input logic [3:0] D0, D1, D2, D3,
  input logic [1:0] S0, S1,
  input logic [3:0] Y
);

  localparam logic [1:0] ZERO = 2'b00, ONE = 2'b01;

  function automatic bit no_x4 (logic [3:0] v);
    return !$isunknown(v);
  endfunction

  // Selects must be single-bit clean (LSB-only) and not X/Z
  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE))
  );

  // Functional correctness (same-cycle)
  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE)) &&
    (S1 == ONE && S0 == ONE) |-> (Y === D3)
  );

  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE)) &&
    (S1 == ONE && S0 == ZERO) |-> (Y === D2)
  );

  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE)) &&
    (S1 == ZERO && S0 == ONE) |-> (Y === D1)
  );

  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE)) &&
    (S1 == ZERO && S0 == ZERO) |-> (Y === D0)
  );

  // Output must not glitch when inputs/selects are stable
  assert property (@(*)
    $stable({D0,D1,D2,D3,S0,S1}) |-> $stable(Y)
  );

  // If all inputs known and selects clean, output must be known
  assert property (@(*)
    (!$isunknown(S0) && (S0 == ZERO || S0 == ONE)) &&
    (!$isunknown(S1) && (S1 == ZERO || S1 == ONE)) &&
    no_x4(D0) && no_x4(D1) && no_x4(D2) && no_x4(D3)
    |-> ! $isunknown(Y)
  );

  // Functional coverage: all select combinations propagate correct input
  cover property (@(*)
    (S1 == ONE && S0 == ONE) && (Y === D3)
  );
  cover property (@(*)
    (S1 == ONE && S0 == ZERO) && (Y === D2)
  );
  cover property (@(*)
    (S1 == ZERO && S0 == ONE) && (Y === D1)
  );
  cover property (@(*)
    (S1 == ZERO && S0 == ZERO) && (Y === D0)
  );

endmodule

// Bind to DUT
bind mux4to1 mux4to1_sva i_mux4to1_sva (.*);