// SVA for PulseGenerator — concise, high-quality checks
module PulseGenerator_sva (
  input logic        clk,
  input logic        rst,
  input logic [31:0] N,
  input logic [31:0] counter,
  input logic        out
);
  default clocking @(posedge clk); endclocking

  // Environment assumptions (can be turned into asserts if desired)
  assume property (disable iff (rst) $stable(N));         // N does not change during operation
  assume property (disable iff (rst) N != 32'd0);         // avoid N-1 underflow / zero-length period

  // Reset behavior (synchronous reset)
  assert property (@(posedge clk) rst |-> (counter==32'd0 && out==1'b0));

  // Known-good values after reset
  assert property (disable iff (rst) !$isunknown({N,counter,out}));

  // Counter always in range [0, N-1]
  assert property (disable iff (rst) counter < N);

  // Normal increment path (no wrap): next counter = prev + 1, out=0
  assert property (disable iff (rst)
    (counter != N-1) |=> (counter == $past(counter)+32'd1 && out==1'b0)
  );

  // Wrap path: on N-1, next cycle counter=0 and out pulses high
  assert property (disable iff (rst)
    (counter == N-1) |=> (counter == 32'd0 && out==1'b1)
  );

  // out only when wrapping, and is single-cycle
  assert property (disable iff (rst) out |-> ($past(counter) == N-1));
  assert property (disable iff (rst) out |=> !out);

  // Exact periodicity: pulses spaced by exactly N cycles with no intermediate highs
  assert property (disable iff (rst) out |-> (!out)[*(N-1)] ##1 out);

  // Coverage
  cover property (disable iff (rst) out);                 // see at least one pulse
  cover property (disable iff (rst) out ##N out);         // see two pulses N cycles apart
endmodule

bind PulseGenerator PulseGenerator_sva sva (.*);