// SVA for dffrl: synchronous active-low reset DFF with scan mux
module dffrl_sva #(parameter SIZE=1)
(
  input  logic                  clk,
  input  logic                  rst_l,
  input  logic                  se,
  input  logic [SIZE-1:0]       din,
  input  logic [SIZE-1:0]       si,
  input  logic [SIZE-1:0]       q,
  input  logic [SIZE-1:0]       so
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: on clk with reset low, q is all-zero
  assert property ( !rst_l |-> (q == '0) );

  // Mux correctness when not in reset
  assert property ( rst_l |-> (q == (se ? si : din)) );

  // Scan-out mirrors q
  assert property ( so == q );

  // No glitches between clock edges (q, so only change on posedge)
  assert property (@(negedge clk) $stable(q) && $stable(so));

  // X-propagation guards when values are used
  assert property ( rst_l && !se |-> !$isunknown(din) );
  assert property ( rst_l &&  se |-> !$isunknown(si) );
  assert property ( rst_l |-> (!$isunknown(q) && !$isunknown(so)) );

  // Coverage
  cover property ( !rst_l ##1 rst_l );             // reset deasserts
  cover property ( rst_l && !se && $changed(q) );  // functional capture
  cover property ( rst_l &&  se && $changed(q) );  // scan capture
  cover property ( $rose(se) );                    // enter scan mode
  cover property ( $fell(se) );                    // exit scan mode

endmodule

// Bind into DUT
bind dffrl dffrl_sva #(.SIZE(SIZE)) u_dffrl_sva (.*);