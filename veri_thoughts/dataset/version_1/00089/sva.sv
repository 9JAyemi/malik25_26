// SVA for power_ground_module
module power_ground_module_sva (
  input logic clk,
  input logic rst_n,
  input logic enable,
  input logic VPWR,
  input logic VGND
);

  default clocking cb @(posedge clk); endclocking

  // Async reset immediately forces zeros (allow NBA with ##0)
  assert property (@(negedge rst_n) 1'b1 |-> ##0 (VPWR==1'b0 && VGND==1'b0));

  // Outputs never X/Z at clock edges
  assert property (!$isunknown({VPWR,VGND}));

  // VGND is always 0
  assert property (VGND == 1'b0);

  // During reset, outputs stay 0
  assert property (!rst_n |-> (VPWR==1'b0 && VGND==1'b0));

  // Functional relation: VPWR equals prior-cycle enable when out of reset
  assert property (disable iff (!rst_n) $past(rst_n) |-> (VPWR == $past(enable)));

  // Never both supplies high
  assert property (!(VPWR && VGND));

  // Coverage
  cover property ($rose(rst_n));                              // reset release seen
  cover property (disable iff (!rst_n) VPWR);                 // VPWR can go high
  cover property (disable iff (!rst_n) $rose(enable) ##1 VPWR);
  cover property (disable iff (!rst_n) $fell(enable) ##1 !VPWR);

endmodule

bind power_ground_module power_ground_module_sva sva_i (
  .clk(clk),
  .rst_n(rst_n),
  .enable(enable),
  .VPWR(VPWR),
  .VGND(VGND)
);