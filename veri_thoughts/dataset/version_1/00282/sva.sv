// SVA for dff_rs
// Checks synchronous priority and next-state behavior; provides concise coverage.

module dff_rs_sva (
  input logic clk,
  input logic rst,
  input logic set,
  input logic d,
  input logic q
);

  default clocking cb @(posedge clk); endclocking

  // Functional next-state: after the clock edge, q must equal mux(rst,set,d)
  property p_next_state;
    ##0 q == (rst ? 1'b0 : (set ? 1'b1 : d));
  endproperty
  assert property (p_next_state)
    else $error("dff_rs: next-state mismatch (rst=%0b,set=%0b,d=%0b,q=%0b)", rst,set,d,q);

  // Explicit priority check when rst and set are both 1: reset dominates -> q=0
  assert property ( (rst && set) |-> ##0 (q==1'b0) )
    else $error("dff_rs: reset must dominate set");

  // If controls/data are known at the edge, q must be known after the update
  assert property ( (!$isunknown({rst,set,d})) |-> ##0 (!$isunknown(q)) )
    else $error("dff_rs: q unknown despite known inputs");

  // Basic branch coverage
  cover property ( rst );                           // reset branch exercised
  cover property ( !rst && set );                   // set branch exercised
  cover property ( !rst && !set && (d==1'b0) );     // data-0 branch exercised
  cover property ( !rst && !set && (d==1'b1) );     // data-1 branch exercised
  cover property ( rst && set ##0 (q==1'b0) );      // simultaneous rst&set -> q=0

  // Output toggle coverage (observed between consecutive posedges)
  cover property ( $rose(q) );
  cover property ( $fell(q) );

  // Data-path tracking covers: q follows d on consecutive data cycles
  cover property ( (!rst && !set && d==1'b0)
                   ##1 (!rst && !set && d==1'b1)
                   ##0 (q==1'b1) );

  cover property ( (!rst && !set && d==1'b1)
                   ##1 (!rst && !set && d==1'b0)
                   ##0 (q==1'b0) );

endmodule

// Bind into DUT
bind dff_rs dff_rs_sva u_dff_rs_sva (.clk(clk), .rst(rst), .set(set), .d(d), .q(q));