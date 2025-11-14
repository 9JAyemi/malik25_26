// SVA for ldly2us
module ldly2us_sva(input logic clk, reset, in, p, l, input logic [6:0] r);
  localparam logic [6:0] MAX = 7'd100;

  // Reset behavior (async reset must hold state cleared when observed on clk)
  assert property (@(posedge clk) reset |-> (r==7'd0 && l==1'b0));

  // Combinational definition and invariants
  assert property (@(posedge clk) disable iff (reset) (p == (r == MAX)));
  assert property (@(posedge clk) disable iff (reset) (l == (r != 7'd0)));
  assert property (@(posedge clk) disable iff (reset) (r inside {[7'd0:MAX]}));

  // Priority/next-state behavior
  assert property (@(posedge clk) disable iff (reset) p |=> (r==7'd0 && l==1'b0));        // p wins, clears
  assert property (@(posedge clk) disable iff (reset) (in && !p) |=> (r==7'd1 && l==1'b1)); // start/restart
  assert property (@(posedge clk) disable iff (reset) (r!=7'd0 && !in && !p) |=> (r==$past(r)+7'd1 && l==1'b1));
  assert property (@(posedge clk) disable iff (reset) p |=> !p); // single-cycle pulse

  // Exact delay when no restarts
  assert property (@(posedge clk) disable iff (reset)
                   (in && !p) ##1 (!in && !p)[*99] |=> p);
  assert property (@(posedge clk) disable iff (reset) (r==7'd99 && !in) |=> p);

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
                  (in && !p) ##1 (!in && !p)[*99] ##1 p);          // clean 100-cycle delay
  cover property (@(posedge clk) disable iff (reset)
                  (in && !p) ##[1:50] (in && !p) ##[1:200] p);     // mid-count restart, then complete
  cover property (@(posedge clk) disable iff (reset) (p && in));   // coincide in with p (p priority)
endmodule

bind ldly2us ldly2us_sva sva_ldly2us (.*);