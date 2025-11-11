// SVA for sky130_fd_sc_lp__a22o: X == (A1 & A2) | (B1 & B2)
// Bind this to the DUT. Focused, concise, and with full functional coverage.

module sky130_fd_sc_lp__a22o_sva;

  // Time-zero check to catch stuck/wrong X even if no activity occurs
  initial begin
    assert (X === ((A1 & A2) | (B1 & B2)))
      else $error("a22o func mismatch at t=0: X=%b A1=%b A2=%b B1=%b B2=%b",
                  X, A1, A2, B1, B2);
  end

  // Sample on any relevant activity (inputs or output)
  default clocking cb @ (A1 or A2 or B1 or B2 or X); endclocking

  // Functional equivalence (4-state exact) and structural checks
  property p_func;   X === ((A1 & A2) | (B1 & B2)); endproperty
  assert property (p_func)
    else $error("a22o func mismatch: X=%b A1=%b A2=%b B1=%b B2=%b",
                X, A1, A2, B1, B2);

  // Internal net equivalence to primitives (checks AND/OR/BUF correctness)
  // These names are from the DUT; binding gives access.
  assert property (and0_out   === (B1 & B2))
    else $error("and0_out mismatch: and0_out=%b B1=%b B2=%b", and0_out, B1, B2);
  assert property (and1_out   === (A1 & A2))
    else $error("and1_out mismatch: and1_out=%b A1=%b A2=%b", and1_out, A1, A2);
  assert property (or0_out_X  === (and1_out | and0_out))
    else $error("or0_out_X mismatch: or0_out_X=%b and1_out=%b and0_out=%b",
                or0_out_X, and1_out, and0_out);
  assert property (X === or0_out_X)
    else $error("buf mismatch: X=%b or0_out_X=%b", X, or0_out_X);

  // Known-in/known-out: if all inputs known, X must be known
  assert property (!$isunknown({A1,A2,B1,B2}) |-> !$isunknown(X))
    else $error("Unknown X with known inputs: X=%b A1=%b A2=%b B1=%b B2=%b",
                X, A1, A2, B1, B2);

  // Compact full truth-table coverage (all 16 input combinations)
  genvar gi;
  for (gi = 0; gi < 16; gi++) begin : TT
    localparam logic [3:0] pat = logic'(gi[3:0]);
    cover property ({A1,A2,B1,B2} === pat);
  end

  // Output toggle coverage
  cover property ($rose(X));
  cover property ($fell(X));

  // Per-input activity coverage
  cover property ($changed(A1));
  cover property ($changed(A2));
  cover property ($changed(B1));
  cover property ($changed(B2));

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__a22o sky130_fd_sc_lp__a22o_sva a22o_sva_i();