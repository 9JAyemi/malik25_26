// SVA for dffsi_4
module dffsi_4_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  init,
  input logic [3:0]  d,
  input logic [3:0]  q
);
  // Functional correctness: next-cycle q equals selected input on current cycle
  assert property (@(posedge clk) 1'b1 |=> q == (reset ? init : d));

  // No glitches between rising edges (q only updates on posedge)
  assert property (@(negedge clk) $stable(q));

  // Coverage: exercise reset path
  cover property (@(posedge clk) reset ##1 (q == $past(init)));

  // Coverage: exercise data path with a change
  cover property (@(posedge clk) !reset && $changed(d) ##1 (q == $past(d)));

  // Per-bit toggle coverage through data path
  genvar i;
  generate
    for (i=0; i<4; i++) begin : COV_BITS
      cover property (@(posedge clk) !reset && $rose(d[i]) ##1 $rose(q[i]));
      cover property (@(posedge clk) !reset && $fell(d[i]) ##1 $fell(q[i]));
    end
  endgenerate
endmodule

// Bind to DUT
bind dffsi_4 dffsi_4_sva sva (.*);