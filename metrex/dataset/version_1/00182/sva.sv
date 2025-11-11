// SVA for delay_800ns
module delay_800ns_sva #(parameter int PULSE_CYCLES = 201,
                         parameter int MAX_COUNT    = 200)
(
  input logic        clk,
  input logic        reset,
  input logic        in,
  input logic        p,
  input logic [31:0] count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset dominance (checked even while reset is asserted)
  assert property (@(posedge clk) reset |-> (p==0 && count==0));

  // Triggering: when idle and 'in' is 1, p must assert immediately
  assert property ( (in && !p) |-> p );

  // p can only rise when in==1 and count is cleared
  assert property ( $rose(p) |-> (in && count==0) );

  // Exact pulse length: p stays high for exactly 201 cycles, then deasserts
  assert property ( $rose(p) |-> p[*PULSE_CYCLES] ##1 !p );

  // Count progresses while p stays high
  assert property ( p && $past(p) |-> count == $past(count) + 1 );

  // Bounds on count
  assert property ( count <= MAX_COUNT );
  assert property ( p |-> (count <= MAX_COUNT) );

  // Falling edge happens only after count reached MAX_COUNT; then count clears
  assert property ( $fell(p) |-> ($past(count) == MAX_COUNT) && (count == 0) );

  // Basic X-checks (optional but useful)
  assert property ( !$isunknown({p,count}) );

  // Coverage
  cover property ( $rose(p) );
  cover property ( $rose(p) ##PULSE_CYCLES $fell(p) );
  // Back-to-back pulses with 1-cycle gap (in held high across boundary)
  cover property ( $rose(p) ##PULSE_CYCLES $fell(p) ##1 (in && !p) ##0 $rose(p) );
endmodule

bind delay_800ns delay_800ns_sva sva_i(.clk(clk), .reset(reset), .in(in), .p(p), .count(count));