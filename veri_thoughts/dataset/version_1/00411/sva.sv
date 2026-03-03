// SVA for lfsr_counter
// Bind this module to the DUT to check/cover key behaviors concisely.

module lfsr_counter_sva #(
  parameter int SIZE = 4
)(
  input logic                   clk,
  input logic                   reset, // active-low async
  input logic                   ena,
  input logic [SIZE-1:0]        out
);

  // Sanity: implementation uses taps [SIZE-1] and [SIZE-2]
  initial if (SIZE < 2) $error("lfsr_counter: SIZE must be >= 2");

  default clocking cb @(posedge clk); endclocking
  // Disable most checks while reset is asserted low
  default disable iff (!reset)

  // Asynchronous reset must drive zero immediately and hold zero while low
  assert property (@(negedge reset) out == '0)
    else $error("out not zero on reset assertion");
  assert property (@(posedge clk) !reset |-> out == '0)
    else $error("out not held at zero while reset low");

  // No X/Z on out after reset deasserted
  assert property (!$isunknown(out))
    else $error("out unknown while reset high");

  // Hold when disabled
  assert property (!ena |-> out == $past(out))
    else $error("out changed while ena==0");

  // Next-state function when enabled
  assert property (ena |-> out == { $past(out[SIZE-2:0]),
                                    $past(out[SIZE-1]) ^ $past(out[SIZE-2]) })
    else $error("LFSR next-state mismatch when ena==1");

  // Basic functional coverage
  cover property (@(negedge reset) 1);               // reset asserted
  cover property (@(posedge reset) 1);               // reset deasserted
  cover property (reset && !ena);                    // hold condition seen
  cover property (reset && ena);                     // update condition seen
  cover property (reset && ena ##1
                  out == { $past(out[SIZE-2:0]),
                          $past(out[SIZE-1]) ^ $past(out[SIZE-2]) }); // update took effect
  // Exercise both feedback XOR outcomes (if reachable/seeding allows)
  cover property (reset && ((out[SIZE-1] ^ out[SIZE-2]) == 1'b0));
  cover property (reset && ((out[SIZE-1] ^ out[SIZE-2]) == 1'b1));

endmodule

// Bind into the DUT
bind lfsr_counter lfsr_counter_sva #(.SIZE(SIZE)) lfsr_counter_sva_b (
  .clk(clk), .reset(reset), .ena(ena), .out(out)
);