// SVA for two_input_and. Bind this to the DUT.
// Focused, race-safe checks with full functional and toggle coverage.

module two_input_and_sva (input logic a, b, y);

  // Simple, delta-cycle-safe combinational equivalence check
  always_comb assert #0 (y === (a & b))
    else $error("AND mismatch: y=%b a=%b b=%b", y, a, b);

  // Flag unknowns on interface
  assert property (@(posedge a or negedge a) !$isunknown(a))
    else $error("Input a went X/Z");
  assert property (@(posedge b or negedge b) !$isunknown(b))
    else $error("Input b went X/Z");

  // If inputs are known, output must be known (no spurious X/Z)
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   (!$isunknown({a,b})) |-> ##0 !$isunknown(y))
    else $error("y is X/Z while inputs are known: a=%b b=%b y=%b", a, b, y);

  // Functional truth-table coverage (race-safe via ##0)
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0
                  (a===1'b0 && b===1'b0 && y===1'b0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0
                  (a===1'b0 && b===1'b1 && y===1'b0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0
                  (a===1'b1 && b===1'b0 && y===1'b0));
  cover property (@(posedge a or negedge a or negedge b or posedge b) ##0
                  (a===1'b1 && b===1'b1 && y===1'b1));

  // Output toggle coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0 $rose(y));
  cover property (@(posedge a or negedge a or posedge b or negedge b) ##0 $fell(y));

endmodule

bind two_input_and two_input_and_sva sva_inst (.a(a), .b(b), .y(y));