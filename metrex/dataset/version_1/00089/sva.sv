// SVA for digital_delay_line
// Concise, high-quality checks with essential coverage.
// Bind these assertions to the DUT.

module digital_delay_line_sva #(parameter int delay = 10)
(
  input  logic        clk,
  input  logic        in,
  input  logic        out,
  input  integer      count,
  input  logic [7:0]  register
);

  default clocking cb @(posedge clk); endclocking
  // Disable assertions while count is unknown (e.g., at time 0)
  default disable iff ($isunknown(count));

  // Sanity: count stays in 0..delay
  assert property (count >= 0 && count <= delay)
    else $error("count out of range 0..delay");

  // When not updating (count < delay): next count increments; register/out hold
  assert property ( (count < delay) |=> (count == $past(count) + 1 && $stable(register) && $stable(out)) )
    else $error("Increment/hold behavior violated when count < delay");

  // When updating (count >= delay): next count resets; out takes prior register[0]; register samples in
  assert property ( (count >= delay) |=> (count == 0 &&
                                          out == $past(register[0]) &&
                                          register == $past(in)) )
    else $error("Update behavior violated when count >= delay");

  // Register width-extension check: MSBs must be zero after an update
  assert property ( (count >= delay) |=> (register[7:1] == '0) )
    else $error("register[7:1] not zero after assignment from 1-bit input");

  // Exact cadence: updates occur every delay+1 cycles (with exactly 'delay' non-update cycles in between)
  assert property ( (count >= delay) |-> ( (count < delay) [*delay] ##1 (count >= delay) ) )
    else $error("Update cadence is not exactly delay+1 cycles");

  // Functional latency of the implemented mechanism:
  // On an update, out equals in from the previous update boundary (delay+1 cycles earlier)
  assert property ( (count >= delay) |=> (out == $past(in, delay+1)) )
    else $error("out does not match in delayed by delay+1 update periods");

  // Basic coverage

  // See at least one update
  cover property (count >= delay);

  // Observe a full cycle: update -> delay stable cycles -> update
  cover property ( (count >= delay) ##1 (count < delay) [*delay] ##1 (count >= delay) );

  // Observe out change on an update (if data toggles)
  cover property ( (count >= delay) && $changed(out) );

endmodule

// Bind to all instances of the DUT
bind digital_delay_line digital_delay_line_sva #(.delay(delay))
  digital_delay_line_sva_i (.clk(clk), .in(in), .out(out), .count(count), .register(register));