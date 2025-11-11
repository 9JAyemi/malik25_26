// SVA for delay_block
// Bind into DUT to check/cover key behaviors concisely

module delay_block_sva #(
  parameter int unsigned delay = 10
)(
  input logic clk,
  input logic in,
  input logic out,
  input logic [31:0] count,
  input logic delayed_in
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic invariants
  assert property (count <= delay);                         // saturates at delay
  assert property (delayed_in == $past(in));                // tracks input 1-cycle

  // Counter behavior
  assert property ($changed(in) |=> count == 0);            // reset on input change
  assert property ($stable(in) && $past(count) < delay
                   |=> count == $past(count)+1);            // increment while < delay
  assert property ($stable(in) && $past(count) >= delay
                   |->  count == $past(count));             // hold when saturated

  // Output behavior: no early change, correct update, alignment
  assert property ($past(count) < delay |-> out == $past(out));              // cannot change early
  assert property ($past(count) >= delay |-> out == $past(delayed_in));      // updates with delayed_in
  assert property ($stable(in) && $past(count) >= delay |-> out == in);      // equals in when stable and ready
  assert property ($changed(out) |-> $past(count) >= delay);                 // any out change implies ready

  // Delay guarantee: if in holds for delay cycles after a change, out matches next cycle
  assert property ($changed(in) |-> $stable(in)[*delay] ##1 (out == in));

  // Coverage
  cover property ($changed(in) ##1 $stable(in)[*delay] ##1 (out == in));     // exercised programmed delay
  cover property ($changed(in) ##[1:delay] $changed(in));                    // back-to-back changes within window
endmodule

bind delay_block delay_block_sva #(.delay(delay))
  delay_block_sva_i (.clk(clk), .in(in), .out(out), .count(count), .delayed_in(delayed_in));