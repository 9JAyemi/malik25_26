// SVA binders for the given DUTs. Concise, high-signal-coverage, combinational-safe.
// Drop these in a separate .sv file and compile with the DUT. No TB code required.

// =============== min_module assertions ===============
bind min_module min_module_sva;
module min_module_sva;

  // Structural correctness of staged mins and final output
  assert property (@(*) ab_min  == ((a < b)  ? a : b)) else $error("ab_min incorrect");
  assert property (@(*) cd_min  == ((c < d)  ? c : d)) else $error("cd_min incorrect");
  assert property (@(*) abcd_min== ((ab_min < cd_min) ? ab_min : cd_min)) else $error("abcd_min incorrect");
  assert property (@(*) min == (((a < b) ? a : b) < ((c < d) ? c : d) ? ((a < b) ? a : b) : ((c < d) ? c : d)))
    else $error("min != min(a,b,c,d)");

  // X-prop hygiene: if inputs known, output must be known
  assert property (@(*) !$isunknown({a,b,c,d}) |-> !$isunknown(min))
    else $error("min X/Z with known inputs");

  // Functional coverage
  cover property (@(*) (a < b));
  cover property (@(*) (a == b));
  cover property (@(*) (c < d));
  cover property (@(*) (c == d));
  cover property (@(*) (((a < b) ? a : b) < ((c < d) ? c : d)));
  // Each unique minimum once
  cover property (@(*) (a < b && a < c && a < d));
  cover property (@(*) (b < a && b < c && b < d));
  cover property (@(*) (c < a && c < b && c < d));
  cover property (@(*) (d < a && d < b && d < c));
  // Tie cases across pairs
  cover property (@(*) (a == b && a <= c && a <= d));
  cover property (@(*) (c == d && c <= a && c <= b));

endmodule


// =============== add_module assertions ===============
bind add_module add_module_sva;
module add_module_sva;

  // Sum must be low 8 bits of full 9-bit add
  assert property (@(*) sum == x_plus_y[7:0]) else $error("sum mismatch");

  // Unsigned carry out must indicate overflow for addition
  assert property (@(*) overflow == x_plus_y[8])
    else $error("overflow should equal unsigned carry out");

  // Sanity on difference wires (as modeled)
  assert property (@(*) x_minus_y == ({1'b0,x} - {1'b0,y})) else $error("x_minus_y mismatch");
  assert property (@(*) y_minus_x == ({1'b0,y} - {1'b0,x})) else $error("y_minus_x mismatch");

  // X-prop hygiene: if inputs known, outputs must be known
  assert property (@(*) !$isunknown({x,y}) |-> !$isunknown({sum,overflow}))
    else $error("sum/overflow X/Z with known inputs");

  // Functional coverage
  cover property (@(*) (x_plus_y[8] == 1'b1)); // unsigned overflow occurs
  cover property (@(*) (x_plus_y[8] == 1'b0)); // no overflow
  cover property (@(*) (x == 8'hFF && y == 8'h01)); // classic wrap to 0
  cover property (@(*) (x == 8'h80 && y == 8'h80)); // signed overflow scenario
  cover property (@(*) (sum == 8'h00));
  cover property (@(*) (sum == 8'hFF));

endmodule


// =============== top_module assertions ===============
bind top_module top_module_sva;
module top_module_sva;

  // Correct muxing of result by select
  assert property (@(*) (select -> result == min_output))
    else $error("result != min_output when select=1");
  assert property (@(*) (!select -> result == add_output))
    else $error("result != add_output when select=0");

  // Overflow must be directly from add_inst
  assert property (@(*) overflow == add_inst.overflow)
    else $error("overflow not forwarded from add_inst");

  // X-prop hygiene: if driving sources known, result must be known
  assert property (@(*) (select && !$isunknown(min_output)) |-> !$isunknown(result))
    else $error("result X/Z with known min_output when select=1");
  assert property (@(*) (!select && !$isunknown(add_output)) |-> !$isunknown(result))
    else $error("result X/Z with known add_output when select=0");

  // Functional coverage
  cover property (@(*) select == 1'b0);
  cover property (@(*) select == 1'b1);
  cover property (@(*) (select && result == min_output));
  cover property (@(*) (!select && result == add_output));

endmodule