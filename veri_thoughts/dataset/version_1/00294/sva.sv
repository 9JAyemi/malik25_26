// SVA for counter
module counter_sva #(parameter int WIDTH=4)
(
  input logic              CLK,
  input logic              RST,
  input logic              enable,
  input logic [WIDTH-1:0]  count_out
);

  default clocking cb @(posedge CLK); endclocking

  // Control sanity
  assert property (!$isunknown(RST) && !$isunknown(enable))
    else $error("counter: control inputs have X/Z");

  // Synchronous reset dominates and drives zero
  assert property (RST |-> (count_out == '0))
    else $error("counter: count_out not zero during RST");

  // When not in reset: increment on enable
  assert property (disable iff (RST) (enable |-> (count_out == $past(count_out) + 1'b1)))
    else $error("counter: increment mismatch");

  // When not in reset: hold when disabled
  assert property (disable iff (RST) (!enable |-> (count_out == $past(count_out))))
    else $error("counter: held value changed without enable");

  // Explicit wrap-around check (redundant with increment, but makes intent clear)
  assert property (disable iff (RST) (enable && ($past(count_out) == {WIDTH{1'b1}}) |-> (count_out == '0)))
    else $error("counter: wrap-around failed");

  // Output known when active (no X/Z after reset deasserted)
  assert property (!RST |-> !$isunknown(count_out))
    else $error("counter: count_out has X/Z when not in reset");

  // Coverage
  cover property (RST);                                            // saw reset
  cover property (disable iff (RST) enable);                       // saw increment opportunity
  cover property (disable iff (RST) !enable);                      // saw hold opportunity
  cover property (disable iff (RST) (enable && $past(count_out)=={WIDTH{1'b1}} && count_out=='0)); // wrap event
  cover property (RST && enable && count_out=='0);                 // simultaneous RST & enable

endmodule

bind counter counter_sva #(.WIDTH(4)) counter_sva_i (.*);