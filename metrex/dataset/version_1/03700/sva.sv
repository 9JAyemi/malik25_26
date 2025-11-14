// SVA for reset_sync. Bind this to the DUT.
// Focus: 2-FF pipeline behavior, output relation, timing, no glitches/X, and edge mapping.

module reset_sync_sva (
  input logic       clk,
  input logic       rst,
  input logic       rst_sync,
  input logic [1:0] rst_sync_reg
);

  default clocking cb @(posedge clk); endclocking

  // Track past-valid for $past depth gating
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // 2-FF pipeline must equal delayed rst history
  assert property (past2 |-> rst_sync_reg == { $past(rst,1), $past(rst,2) });

  // Combinational relation
  assert property (rst_sync == ~rst_sync_reg[1]);

  // High-level spec: output equals inverted rst delayed by 2 cycles
  assert property (past2 |-> rst_sync == ~ $past(rst,2));

  // No X/Z on internal regs or output after pipeline is initialized
  assert property (past2 |-> !$isunknown({rst_sync_reg, rst_sync}));

  // No glitches between clock edges (regs/output only change on posedge)
  assert property (@(negedge clk) $stable({rst_sync_reg, rst_sync}));

  // Edge mapping: deassert/assert after exactly 2 cycles
  assert property (past2 && $rose(rst) |-> ##2 $fell(rst_sync));
  assert property (past2 && $fell(rst) |-> ##2 $rose(rst_sync));

  // Coverage: both edges and a 1-cycle pulse propagation
  cover property (past2 && $rose(rst) ##2 $fell(rst_sync));
  cover property (past2 && $fell(rst) ##2 $rose(rst_sync));
  cover property (past2 && $rose(rst) ##1 $fell(rst) ##2 $fell(rst_sync) ##1 $rose(rst_sync));

endmodule

// Example bind
bind reset_sync reset_sync_sva sva (
  .clk(clk),
  .rst(rst),
  .rst_sync(rst_sync),
  .rst_sync_reg(rst_sync_reg)
);