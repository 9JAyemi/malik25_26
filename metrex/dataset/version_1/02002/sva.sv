// SVA for reset_module
module reset_module_sva(input logic clk, rst, rst_n);

  // Sample on negedge, since DUT updates on negedge
  default clocking cb @(negedge clk); endclocking

  // While rst is asserted, rst_n must be held low at each negedge
  assert property (rst |-> !rst_n);

  // Deassertion latency: if rst stays low, rst_n releases exactly 2 negedges after $fell(rst)
  assert property (disable iff (rst)
                   $fell(rst) |-> (!rst_n ##1 !rst_n ##1 rst_n));

  // Once low is released, rst_n must not fall again while rst is low
  assert property (disable iff (rst) !$fell(rst_n));

  // rst_n only updates on negedge clk (no posedge changes/glitches)
  assert property (@(posedge clk) !$changed(rst_n));

  // rst_n may only rise when rst is low
  assert property ($rose(rst_n) |-> !rst);

  // Coverage: observe a full deassert sequence and a reassert after release
  cover property ($fell(rst) ##1 !rst_n ##1 rst_n);
  cover property (rst ##1 !rst ##2 rst ##1 !rst_n);

endmodule

// Bind into DUT
bind reset_module reset_module_sva sva_reset_module (.*);