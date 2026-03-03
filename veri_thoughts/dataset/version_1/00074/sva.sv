// SVA for jAsyncCntrDFlipFlop and jAsynchronousCounter
// Focused, concise checks with essential coverage

// Bind-time SVA for the DFF cell
module jAsyncCntrDFlipFlop_sva(input logic q, qbar, clk, rst, d);
  // Track first valid sample on clk after reset
  bit seen_clk;
  always @(posedge clk or posedge rst) if (rst) seen_clk <= 1'b0; else seen_clk <= 1'b1;

  // qbar must always be complement of q (sampled at activity)
  assert property (@(posedge clk or posedge rst) qbar === ~q);

  // Asynchronous reset dominates and holds q low while asserted
  assert property (@(posedge rst) q == 1'b0);
  assert property (@(posedge clk)  rst |-> q == 1'b0);

  // DFF semantic: on clk with rst deasserted, q captures previous d
  assert property (@(posedge clk) disable iff (rst || !seen_clk) q === $past(d));

  // In this design, DFF behaves as a T-flop (d == ~q), so q toggles each clk when not in reset
  assert property (@(posedge clk) disable iff (rst || !seen_clk) q === ~$past(q));

  // No X/Z on observable outputs at activity
  assert property (@(posedge clk or posedge rst) !$isunknown({q,qbar}));

  // Coverage: both edges occur on q when running
  cover property (@(posedge clk) disable iff (rst) $rose(q));
  cover property (@(posedge clk) disable iff (rst) $fell(q));
endmodule

bind jAsyncCntrDFlipFlop jAsyncCntrDFlipFlop_sva u_dff_sva(.q(q), .qbar(qbar), .clk(clk), .rst(rst), .d(d));


// Bind-time SVA for the 4-bit asynchronous counter
module jAsynchronousCounter_sva(
  input  logic        clk, rst,
  input  logic [3:0]  count,
  input  logic [3:0]  countbar
);
  // Per-local-clock "seen" flags for safe $past usage
  bit seen_clk0, seen_clk1, seen_clk2, seen_clk3;
  // Stage 0 uses top clk
  always @(posedge clk      or posedge rst) if (rst) seen_clk0 <= 1'b0; else seen_clk0 <= 1'b1;
  // Stage 1..3 use ripple clocks
  always @(posedge count[0] or posedge rst) if (rst) seen_clk1 <= 1'b0; else seen_clk1 <= 1'b1;
  always @(posedge count[1] or posedge rst) if (rst) seen_clk2 <= 1'b0; else seen_clk2 <= 1'b1;
  always @(posedge count[2] or posedge rst) if (rst) seen_clk3 <= 1'b0; else seen_clk3 <= 1'b1;

  // Reset drives all zeros; mirror outputs are complements
  assert property (@(posedge rst) count == 4'b0000);
  assert property (@(posedge clk or posedge count[0] or posedge count[1] or posedge count[2] or posedge rst)
                   countbar === ~count);

  // Each stage toggles on posedge of its local clock when not in reset (ripple behavior)
  assert property (@(posedge clk)      disable iff (rst || !seen_clk0) count[0] === ~$past(count[0]));
  assert property (@(posedge count[0]) disable iff (rst || !seen_clk1) count[1] === ~$past(count[1]));
  assert property (@(posedge count[1]) disable iff (rst || !seen_clk2) count[2] === ~$past(count[2]));
  assert property (@(posedge count[2]) disable iff (rst || !seen_clk3) count[3] === ~$past(count[3]));

  // No X/Z on observable buses at key activity points
  assert property (@(posedge clk or posedge count[0] or posedge count[1] or posedge count[2] or posedge rst)
                   !$isunknown({count, countbar}));

  // Coverage: observe ripple propagation through stages on their respective clocks
  cover property (@(posedge clk)      disable iff (rst) $rose(count[0]));
  cover property (@(posedge count[0]) disable iff (rst) $rose(count[1]));
  cover property (@(posedge count[1]) disable iff (rst) $rose(count[2]));
  cover property (@(posedge count[2]) disable iff (rst) $rose(count[3]));

  // Coverage: LSB only toggles (no ripple) on alternate input clocks
  cover property (@(posedge clk) disable iff (rst) $fell(count[0]));
endmodule

bind jAsynchronousCounter jAsynchronousCounter_sva u_cnt_sva(.*);