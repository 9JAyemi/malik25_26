// SVA for mux2x1 and mux4x1
// Bind these to the DUT; uses event-based sampling with ##0 to avoid delta races.

module mux2x1_sva (input logic a, b, s, y);
  // Sample on any input/output edge; check after ##0 to allow combinational settle
  default clocking @(posedge a or negedge a or
                     posedge b or negedge b or
                     posedge s or negedge s or
                     posedge y or negedge y); endclocking

  // Functional equivalence
  assert property (1 |-> ##0 (y === (s ? b : a)))
    else $error("mux2x1 func mismatch: y != (s?b:a)");

  // Useful X-robustness: identical inputs force y regardless of s
  assert property ((a === b) |-> ##0 (y === a))
    else $error("mux2x1 X-robustness failed when a==b");

  // Coverage: both select paths exercised and observed at y
  cover property (1 |-> ##0 (!s && (y === a)));
  cover property (1 |-> ##0 ( s && (y === b)));
endmodule

bind mux2x1 mux2x1_sva mux2x1_sva_b (.*);


module mux4x1_sva (input logic a, b, c, d, sel0, sel1, y);
  default clocking @(posedge a or negedge a or
                     posedge b or negedge b or
                     posedge c or negedge c or
                     posedge d or negedge d or
                     posedge sel0 or negedge sel0 or
                     posedge sel1 or negedge sel1 or
                     posedge y or negedge y); endclocking

  // Functional equivalence to 4:1 mux truth table
  assert property (1 |-> ##0 (y === (sel1 ? (sel0 ? d : c) : (sel0 ? b : a))))
    else $error("mux4x1 func mismatch");

  // Coverage: all four select combinations observed at y
  cover property (1 |-> ##0 (!sel1 && !sel0 && (y === a)));
  cover property (1 |-> ##0 (!sel1 &&  sel0 && (y === b)));
  cover property (1 |-> ##0 ( sel1 && !sel0 && (y === c)));
  cover property (1 |-> ##0 ( sel1 &&  sel0 && (y === d)));

  // Optional: selectors toggle at least once
  cover property ($changed(sel0));
  cover property ($changed(sel1));
endmodule

bind mux4x1 mux4x1_sva mux4x1_sva_b (.*);