// SVA for bit_counter
// Binds into the DUT and checks internal prefix chain, 1-cycle latency, truncation, and basic coverage.

module bit_counter_sva (
  input  logic        clk,
  input  logic [15:0] D,
  input  logic [3:0]  count,
  input  logic [3:0]  P [0:3]   // tap internal prefix nodes
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard (no reset provided)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Helper functions: 6-bit total sum and truncated 4-bit result
  function automatic logic [5:0] sum6(input logic [15:0] d);
    sum6 = d[3:0] + d[7:4] + d[11:8] + d[15:12]; // 0..60 fits in 6 bits
  endfunction
  function automatic logic [3:0] sum4(input logic [15:0] d);
    sum4 = sum6(d)[3:0]; // modulo-16 truncation
  endfunction

  // Internal combinational prefix chain correctness
  assert property (P[0] == D[3:0]);
  assert property (P[1] == (P[0] + D[7:4])[3:0]);
  assert property (P[2] == (P[1] + D[11:8])[3:0]);
  assert property (P[3] == (P[2] + D[15:12])[3:0]);
  assert property (P[3] == sum4(D)); // overall chain == direct nibble-sum mod16

  // Registered output: exactly 1-cycle latency of P[3]
  assert property (disable iff (!past_valid) count == $past(P[3]));

  // Functional equivalence (modulo-16 sum of nibbles, 1-cycle latency)
  assert property (disable iff (!past_valid) count == $past(sum4(D)));

  // X-propagation sanity
  assert property (!$isunknown(P[3]));
  assert property (disable iff (!past_valid) !$isunknown(count));

  // Coverage
  cover property (past_valid && $past(D) == 16'h0000 && count == 4'h0);   // zero case
  cover property (past_valid && $past(D) == 16'hFFFF && count == 4'hC);   // max-input wrap case (60 -> 12)
  cover property (past_valid && sum6($past(D)) <  6'd16 && count == sum6($past(D))[3:0]); // no overflow
  cover property (past_valid && sum6($past(D)) >= 6'd16 && count == sum6($past(D))[3:0]); // overflow
  cover property (count == 4'h0);
  cover property (count == 4'hF);

endmodule

bind bit_counter bit_counter_sva u_bit_counter_sva (.clk(clk), .D(D), .count(count), .P(P));