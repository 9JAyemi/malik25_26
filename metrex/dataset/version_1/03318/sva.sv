// SVA for frame_rate. Bind this to the DUT. Focused, concise, high-quality checks.

module frame_rate_sva #(parameter int COUNT_MAX = 2) (
  input  logic        inclk0,
  input  logic        c0, c1, locked,
  input  logic        inclk0_d,
  input  logic        locked_d, locked_dd,
  input  logic        c0_d, c1_d,
  input  logic        c0_dd, c1_dd,
  input  logic        locked_next, c0_next, c1_next,
  input  int          count
);

  default clocking cb @(posedge inclk0); endclocking
  logic past_valid; initial past_valid = 1'b0;
  always_ff @(posedge inclk0) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Counter behavior: count increments until COUNT_MAX, then wraps to 0.
  assert property ( ($past(count) == COUNT_MAX) ? (count == 0) : (count == $past(count)+1) );

  // Delay chains update every cycle.
  assert property (c0_d      == $past(c0_next));
  assert property (c1_d      == $past(c1_next));
  assert property (locked_d  == $past(locked_next));
  assert property (c0_dd     == $past(c0_d));
  assert property (c1_dd     == $past(c1_d));
  assert property (locked_dd == $past(locked_d));
  assert property (inclk0_d  == $past(inclk0));

  // Outputs update only on update cycles; otherwise hold.
  assert property ( (count != COUNT_MAX) |=> $stable({c0,c1,locked}) );

  // On an update cycle, outputs take the prior "next" values.
  assert property ( (count == COUNT_MAX) |=> (c0 == $past(c0_next) && c1 == $past(c1_next) && locked == $past(locked_next)) );

  // Next-state logic updates only on update cycles; otherwise holds.
  assert property ( (count == COUNT_MAX) |=> ( c0_next    == ~ $past(c0_dd)
                                            && c1_next    ==    $past(c0_dd)
                                            && locked_next== (($past(inclk0_d) == $past(locked_dd)) ? 1'b1 : 1'b0) ) );
  assert property ( (count != COUNT_MAX) |=> $stable({c0_next, c1_next, locked_next}) );

  // Outputs can change only if last cycle was an update cycle.
  assert property ( $changed(c0)     |-> $past(count) == COUNT_MAX );
  assert property ( $changed(c1)     |-> $past(count) == COUNT_MAX );
  assert property ( $changed(locked) |-> $past(count) == COUNT_MAX );

  // Coverage: observe update cadence and activity on key outputs.
  cover property ( (count == COUNT_MAX) ##1 (count == 0) ##COUNT_MAX (count == COUNT_MAX) );
  cover property ( $changed(c0) );
  cover property ( $changed(c1) );
  cover property ( $changed(locked) );
  cover property ( $rose(locked) );
  cover property ( $fell(locked) );

endmodule

// Bind into the DUT (inherits the DUT's COUNT_MAX parameter)
bind frame_rate frame_rate_sva #(.COUNT_MAX(COUNT_MAX)) u_frame_rate_sva (.*);