// SVA for jt51_noise_lfsr
// Bind this to the DUT to check behavior and provide coverage.

module jt51_noise_lfsr_sva #(parameter init = 14220)
(
  input logic        clk,
  input logic        rst,
  input logic        base,
  input logic        out,
  input logic [16:0] bb
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X/Z)
  assert property (!$isunknown({rst, base}));                         // inputs known
  assert property (!$isunknown(bb));                                  // state known
  assert property (!$isunknown(out));                                 // output known

  // Output matches MSB of state
  assert property (out == bb[16]);

  // Synchronous reset dominates (regardless of base)
  assert property (rst |-> bb == init[16:0]);

  // Hold when base = 0 (normal operation)
  assert property (!rst && !base |=> bb == $past(bb));

  // LFSR next-state when base = 1 (normal operation)
  assert property (!rst && base |=> bb == { $past(bb[15:0]),
                                            ~($past(bb[16]) ^ $past(bb[13])) });

  // Derived checks on visible output behavior
  assert property (!rst && base |=> out == $past(bb[15]));            // new MSB is old bit[15]
  assert property (!rst && !base |=> $stable(out));                   // output holds when not stepping

  // Functional coverage
  cover property (rst);                                               // reset seen
  cover property (rst ##1 !rst);                                      // reset release
  cover property (!rst && base);                                      // a step occurs
  cover property (!rst && !base);                                     // a hold occurs
  cover property (!rst && base ##1 !rst && base);                     // back-to-back steps
  cover property (!rst && !base ##1 !rst && base);                    // hold then step
  cover property (!rst && base |=> out != $past(out));                // output toggled on a step
  cover property (!rst && base && (~($past(bb[16]) ^ $past(bb[13])))); // feedback = 1 case
  cover property (!rst && base && (~($past(bb[16]) ^ $past(bb[13]))==1'b0)); // feedback = 0 case

endmodule

// Bind into the DUT (place in a package or a separate sv file included in the sim)
// This bind assumes access to internal 'bb' signal.
bind jt51_noise_lfsr
  jt51_noise_lfsr_sva #(.init(init))
  jt51_noise_lfsr_sva_i (
    .clk (clk),
    .rst (rst),
    .base(base),
    .out (out),
    .bb  (bb)
  );