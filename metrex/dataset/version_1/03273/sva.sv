// SVA for signed_adder_overflow_detection
module signed_adder_overflow_detection_sva (
  input  logic              clk,
  input  logic              reset,
  input  logic signed [7:0] a,
  input  logic signed [7:0] b,
  input  logic signed [7:0] s,
  input  logic              ov
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // One-cycle combinational intents
  let sum_now   = $signed(a) + $signed(b);
  let ov_nowexp = (a[7] == b[7]) && (a[7] != sum_now[7]);

  // Reset behavior
  assert property (reset |=> (s == 8'sd0 && ov == 1'b0));

  // Registered datapath correctness
  assert property (1 |=> s == $past(sum_now));

  // Overflow flag correctness
  assert property (1 |=> ov == $past(ov_nowexp));

  // No X/Z on outputs after reset deasserted
  assert property (!$isunknown({s, ov}));

  // Concise functional coverage
  // Any overflow event
  cover property (ov);

  // Positive overflow:  127 + 1 -> -128, ov==1
  cover property ((a == 8'sd127 && b == 8'sd1)  ##1 (ov && s == -128));

  // Negative overflow: -128 + (-1) -> 127, ov==1
  cover property ((a == -8'sd128 && b == -8'sd1) ##1 (ov && s == 127));

  // No-overflow example
  cover property ((a == 8'sd50 && b == 8'sd20) ##1 (!ov && s == 8'sd70));

endmodule

// Bind into DUT
bind signed_adder_overflow_detection signed_adder_overflow_detection_sva sva (.*);