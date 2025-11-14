// SVA for edge_detector
module edge_detector_sva (
  input  logic clk,
  input  logic reset,
  input  logic in,
  input  logic rising_edge,
  input  logic falling_edge,
  input  logic prev_in
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Asynchronous reset clears immediately
  assert property (@(posedge reset) (rising_edge==0 && falling_edge==0 && prev_in==0));

  // While reset is asserted, outputs stay low
  assert property (reset |-> (rising_edge==0 && falling_edge==0));

  // No X/Z after reset
  assert property (!$isunknown({rising_edge, falling_edge, prev_in}));

  // prev_in tracks prior in on active cycles
  assert property ($past(!reset) |-> (prev_in == $past(in)));

  // No change => no pulses
  assert property ((in == $past(in)) |-> !(rising_edge || falling_edge));

  // Exact rise mapping (both directions)
  assert property ((in && !$past(in)) |-> (rising_edge && !falling_edge));
  assert property (rising_edge |-> (in && !$past(in)));

  // Exact fall mapping (both directions)
  assert property ((!in && $past(in)) |-> (!rising_edge && falling_edge));
  assert property (falling_edge |-> (!in && $past(in)));

  // One-cycle pulse width
  assert property (rising_edge |-> ##1 !rising_edge);
  assert property (falling_edge |-> ##1 !falling_edge);

  // Mutual exclusion
  assert property (!(rising_edge && falling_edge));

  // Coverage
  cover property ((in && !$past(in)) && rising_edge);          // saw a rising-edge pulse
  cover property ((!in && $past(in)) && falling_edge);         // saw a falling-edge pulse
  cover property ((in && !$past(in)) ##1 (!in && $past(in)));  // rise then fall on consecutive cycles
endmodule

// Bind to all instances of edge_detector
bind edge_detector edge_detector_sva sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .rising_edge(rising_edge),
  .falling_edge(falling_edge),
  .prev_in(prev_in)
);