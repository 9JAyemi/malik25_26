// SVA checker for umult8
// Bind this to your DUT instance(s)

module umult8_sva
(
  input  logic [0:7]  reg_A,
  input  logic [0:7]  reg_B,
  input  logic [0:15] result,
  // Internals for deeper checks (connected via bind)
  input  logic [0:15] p8a_0,
  input  logic [0:15] p8b_0,
  input  logic [0:15] pt
);

  function automatic logic [0:15] exp_mul (input logic [0:7] a, input logic [0:7] b);
    exp_mul = $unsigned(a) * $unsigned(b);
  endfunction

  // Correctness: when inputs are known, output equals unsigned product and is known
  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B})) |-> (result == exp_mul(reg_A,reg_B) && !$isunknown(result)))
    else $error("umult8: result mismatch");

  // Output changes only when an input changes (pure combinational behavior)
  assert property (@(reg_A or reg_B or result)
                   $changed(result) |-> ($changed(reg_A) || $changed(reg_B)))
    else $error("umult8: spurious result change without input change");

  // result reflects pt after computation (NB assignment completes in same timestep)
  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B})) |-> (result == pt))
    else $error("umult8: result != pt");

  // Internal packing checks (zero-extend into lower half [8:15])
  assert property (@(reg_A or reg_B or result)
                   (!$isunknown(reg_A)) |-> (p8a_0[0:7] == 8'b0 && p8a_0[8:15] == reg_A[0:7]))
    else $error("umult8: p8a_0 packing incorrect");

  assert property (@(reg_A or reg_B or result)
                   (!$isunknown(reg_B)) |-> (p8b_0[0:7] == 8'b0 && p8b_0[8:15] == reg_B[0:7]))
    else $error("umult8: p8b_0 packing incorrect");

  // Algebraic identities
  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B}) && (reg_A == 8'd0 || reg_B == 8'd0)) |-> (result == 16'd0))
    else $error("umult8: zero identity violated");

  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B}) && reg_A == 8'd1) |-> (result == {8'b0,reg_B}))
    else $error("umult8: multiplicative identity A=1 violated");

  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B}) && reg_B == 8'd1) |-> (result == {8'b0,reg_A}))
    else $error("umult8: multiplicative identity B=1 violated");

  // Basic X-prop: known inputs imply known output
  assert property (@(reg_A or reg_B or result)
                   (!$isunknown({reg_A,reg_B})) |-> !$isunknown(result))
    else $error("umult8: X/Z on result with known inputs");

  // Coverage (key corners and high-bit activation)
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_A == 8'd0 && reg_B != 8'd0));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_B == 8'd0 && reg_A != 8'd0));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_A == 8'd1));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_B == 8'd1));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_A == 8'd255 && reg_B == 8'd255));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) && reg_A == 8'd128 && reg_B == 8'd128));
  cover property (@(reg_A or reg_B) (!$isunknown({reg_A,reg_B}) ##0 result[0]); // MSB set
endmodule

// Bind into DUT (connect internals for stronger checking)
bind umult8 umult8_sva u_umult8_sva (
  .reg_A (reg_A),
  .reg_B (reg_B),
  .result(result),
  .p8a_0 (p8a_0),
  .p8b_0 (p8b_0),
  .pt    (pt)
);