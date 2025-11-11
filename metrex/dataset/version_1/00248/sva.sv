// SVA for bcd_counter: concise, high-quality checks and coverage
module bcd_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [2:0]  ena,
  input  logic [15:0] q,
  input  logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Synchronous reset effect (same-cycle)
  assert property (@(posedge clk) reset |-> ##0 (count==4'd0 && ena==3'b000 && q==16'h0000));

  // Count increments modulo 16 when not in reset
  assert property (count == $past(count) + 4'd1);

  // ena shifts left inserting 1 (saturates at 3'b111)
  assert property (ena == {$past(ena)[1:0], 1'b1});

  // q is valid BCD and matches count
  assert property (q[3:0] < 10 && q[7:4] < 10 && q[11:8] == 0 && q[15:12] == 0);
  assert property ((q[3:0] + 10*q[7:4] + 100*q[11:8] + 1000*q[15:12]) == count);

  // No X/Z on observable/state signals out of reset
  assert property (!$isunknown({count, ena, q}));

  // Coverage
  // ena progression after reset: 000 -> 001 -> 011 -> 111
  cover property (@(posedge clk) reset ##1 (!reset && ena==3'b001) ##1 (ena==3'b011) ##1 (ena==3'b111));
  // 4-bit wrap: 15 -> 0
  cover property ($past(count)==4'hF && count==4'h0);
  // Two-digit BCD examples reachable (10 and 15)
  cover property (q==16'h0010);
  cover property (q==16'h0015);
endmodule

// Bind to all instances of bcd_counter, including inside top_module
bind bcd_counter bcd_counter_sva sva_bcd_counter (
  .clk  (clk),
  .reset(reset),
  .ena  (ena),
  .q    (q),
  .count(count)
);