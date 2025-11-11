// SVA checker for mux_2to1
// Bind this to the DUT. Uses event-based sampling and ##0 to check post-delta values.
`ifndef SYNTHESIS
module mux_2to1_sva (
  input logic a,
  input logic b,
  input logic sel,
  input logic y
);

  // Functional equivalence (4-state exact)
  assert property (@(posedge a or negedge a or
                     posedge b or negedge b or
                     posedge sel or negedge sel or
                     posedge y or negedge y)
                   ##0 (y === ((!sel & a) | (sel & b))))
    else $error("mux_2to1: y != ((!sel & a) | (sel & b))");

  // Selected input must drive y immediately
  assert property (@(posedge a or negedge a) (sel==1'b0) |-> ##0 (y === a))
    else $error("mux_2to1: sel=0, y must follow a");
  assert property (@(posedge b or negedge b) (sel==1'b1) |-> ##0 (y === b))
    else $error("mux_2to1: sel=1, y must follow b");

  // Unselected input must not affect y
  assert property (@(posedge b or negedge b) (sel==1'b0) |-> ##0 $stable(y))
    else $error("mux_2to1: sel=0, y must ignore b");
  assert property (@(posedge a or negedge a) (sel==1'b1) |-> ##0 $stable(y))
    else $error("mux_2to1: sel=1, y must ignore a");

  // No X-propagation when inputs are known
  assert property (@(posedge a or negedge a or
                     posedge b or negedge b or
                     posedge sel or negedge sel)
                   (!$isunknown({a,b,sel})) |-> ##0 (!$isunknown(y)))
    else $error("mux_2to1: known inputs produced unknown y");

  // Coverage
  cover property (@(posedge a or negedge a) (sel==1'b0) ##0 (y===a));
  cover property (@(posedge b or negedge b) (sel==1'b1) ##0 (y===b));
  cover property (@(posedge sel)           ##0 (y===b));
  cover property (@(negedge sel)           ##0 (y===a));

endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva(.a(a), .b(b), .sel(sel), .y(y));
`endif