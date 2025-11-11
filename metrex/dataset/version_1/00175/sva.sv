// SVA for dff_5
// Checks: reset/preset priority and values, normal tracking of d, complementarity, and glitch-free outputs.
// Includes concise functional coverage.

module dff_5_sva #(parameter WIDTH=5)
(
  input  logic                 clk,
  input  logic                 rstn,
  input  logic                 prsn,
  input  logic [WIDTH-1:0]     d,
  input  logic [WIDTH-1:0]     q,
  input  logic [WIDTH-1:0]     qn
);

  default clocking cb @(posedge clk); endclocking

  // Helper to avoid first-cycle $past hazards
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset has highest priority
  assert property (!rstn |-> (q == '0 && qn == '1));

  // Preset (active-low) when not in reset
  assert property (rstn && !prsn |-> (q == '1 && qn == '0));

  // Normal operation: track D (ensure previous cycle was also normal and data known)
  assert property (
    past_valid && $past(rstn && prsn) && rstn && prsn &&
    !$isunknown($past(d)) && !$isunknown({q,qn})
    |-> (q == $past(d) && qn == ~$past(d))
  );

  // q and qn are always complementary when known
  assert property ( !$isunknown({q,qn}) |-> (qn == ~q) );

  // No glitches between clock edges (outputs only change on posedge)
  assert property (@(negedge clk) $stable(q) && $stable(qn));

  // Priority when both controls active-low simultaneously: reset wins
  assert property ((!rstn && !prsn) |-> (q == '0 && qn == '1));

  // Functional coverage
  cover property (!rstn);                 // reset taken
  cover property (rstn && !prsn);         // preset taken
  cover property (!rstn && !prsn);        // both low together (priority case)
  cover property (
    past_valid && $past(rstn && prsn) && rstn && prsn && (q != $past(q))
  );                                      // output changed in normal mode
  cover property (
    past_valid && $past(rstn && prsn) && rstn && prsn && (q == '0)
  );                                      // loaded all-zeros in normal mode
  cover property (
    past_valid && $past(rstn && prsn) && rstn && prsn && (q == '1)
  );                                      // loaded all-ones in normal mode

endmodule

// Bind into the DUT
bind dff_5 dff_5_sva #(.WIDTH(5)) dff_5_sva_i (
  .clk(clk),
  .rstn(rstn),
  .prsn(prsn),
  .d(d),
  .q(q),
  .qn(qn)
);