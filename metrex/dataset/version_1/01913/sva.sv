// SVA checker for borderscan
module borderscan_sva #(
  parameter int SCREENWIDTH  = 1024,
  parameter int SCREENHEIGHT = 768
)(
  input logic       clk,
  input logic       xstart,
  input logic       xend,
  input logic [9:0] realy,
  input logic       q
);

  default clocking cb @(posedge clk); endclocking

  // Static width sanity (catches likely width bugs)
  initial begin
    assert ($bits(xstart) >= $clog2(SCREENWIDTH))  else $error("xstart width < clog2(SCREENWIDTH)");
    assert ($bits(xend)   >= $clog2(SCREENWIDTH))  else $error("xend width < clog2(SCREENWIDTH)");
    assert ($bits(realy)  >= $clog2(SCREENHEIGHT)) else $error("realy  width < clog2(SCREENHEIGHT)");
  end

  // No X/Z on critical signals
  assert property ( !$isunknown({xstart,xend,realy,q}) );

  // Functional equivalence (simplified boolean form)
  assert property ( q == ((realy < SCREENHEIGHT) && ((xstart == 0) || (xend == SCREENWIDTH-1))) );

  // Negative cases
  assert property ( (realy >= SCREENHEIGHT) |-> !q );
  assert property ( ((realy < SCREENHEIGHT) && (xstart != 0) && (xend != SCREENWIDTH-1)) |-> !q );

  // Positive implications (edges)
  assert property ( ((realy < SCREENHEIGHT) && (xstart == 0))           |-> q );
  assert property ( ((realy < SCREENHEIGHT) && (xend   == SCREENWIDTH-1)) |-> q );

  // Coverage: corners, edges, interior, out-of-range, and q toggles
  cover property ( (realy == 0)                  && (xstart == 0)            && q ); // top-left
  cover property ( (realy == 0)                  && (xend   == SCREENWIDTH-1) && q ); // top-right
  cover property ( (realy == SCREENHEIGHT-1)     && (xstart == 0)            && q ); // bottom-left
  cover property ( (realy == SCREENHEIGHT-1)     && (xend   == SCREENWIDTH-1) && q ); // bottom-right
  cover property ( (realy > 0) && (realy < SCREENHEIGHT-1) && (xstart == 0)            && q ); // left edge
  cover property ( (realy > 0) && (realy < SCREENHEIGHT-1) && (xend   == SCREENWIDTH-1) && q ); // right edge
  cover property ( (realy > 0) && (realy < SCREENHEIGHT-1) && (xstart != 0) && (xend != SCREENWIDTH-1) && !q ); // interior
  cover property ( (realy >= SCREENHEIGHT) && !q ); // out-of-range row
  cover property ( $rose(q) );
  cover property ( $fell(q) );

endmodule

// Bind into DUT
bind borderscan borderscan_sva #(
  .SCREENWIDTH (SCREENWIDTH),
  .SCREENHEIGHT(SCREENHEIGHT)
) u_borderscan_sva (
  .clk   (clk),
  .xstart(xstart),
  .xend  (xend),
  .realy (realy),
  .q     (q)
);