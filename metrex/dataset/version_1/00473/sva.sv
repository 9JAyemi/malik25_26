// SVA for clock_gate_d_ff
// Bind this module or insert inside the DUT. Focuses on safe clock gating and FF behavior.
module clock_gate_d_ff_sva (
  input  logic        clk,
  input  logic        en,
  input  logic        en_ff,
  input  logic [31:0] data,
  input  logic        q
);
  // Recreate gated clock (observability)
  wire gated_clk = clk & en;

  // Sanity: controls/data not X at sampling edges
  assert property (@(posedge clk)       !$isunknown({clk,en,en_ff}));
  assert property (@(posedge gated_clk) !$isunknown(data[0]));

  // Safe gating: no gated posedge except when clk rises with en=1
  assert property (@(posedge gated_clk) $rose(clk) && en);
  // If en is 1 at clk posedge, we must see a gated posedge
  assert property (@(posedge clk) en |-> $rose(gated_clk));
  // If en is 0 at clk posedge, we must NOT see a gated posedge
  assert property (@(posedge clk) !en |-> !$rose(gated_clk));

  // Glitch prevention requirement on en: only change when clk is low
  assert property (@(posedge en or negedge en) !clk);

  // Functional correctness (note: q is 1-bit; RTL truncates data to data[0])
  // Capture when enabled
  assert property (@(posedge gated_clk) en_ff |-> ##1 q == $past(data[0],1,gated_clk));
  // Hold when not enabled
  assert property (@(posedge gated_clk) !en_ff |-> ##1 q == $past(q,1,gated_clk));
  // When gating disabled, q must be stable across clk edges
  assert property (@(posedge clk) !en |-> $stable(q));

  // Coverage
  cover property (@(posedge gated_clk) en_ff && data[0]==1'b0);
  cover property (@(posedge gated_clk) en_ff && data[0]==1'b1);
  cover property (@(posedge gated_clk) !en_ff);
  cover property (@(posedge en) !clk); // legal en rise (clk low)
endmodule

// Example bind (place in a package or testbench):
// bind clock_gate_d_ff clock_gate_d_ff_sva u_sva(.clk(clk), .en(en), .en_ff(en_ff), .data(data), .q(q));