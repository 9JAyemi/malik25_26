// SVA checker for aq_div32x32
// Throughput: 1/cycle, latency: 32 cycles, unsigned divide
module aq_div32x32_sva #(parameter int LAT = 32)
(
  input logic        CLK,
  input logic        RST_N,
  input logic [31:0] DINA,
  input logic [31:0] DINB,
  input logic [31:0] DOUT
);
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST_N)

  // Functional correctness (unsigned): when the divisor captured LAT cycles ago was non-zero
  // and we have LAT cycles out of reset, DOUT must equal the quotient
  assert property (
    RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) != 32'd0)
      |-> DOUT == ($past(DINA, LAT) / $past(DINB, LAT))
  );

  // Basic range/special-case checks (redundant but strong and cheap)
  assert property (
    RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) != 32'd0)
      |-> DOUT <= $past(DINA, LAT)
  );

  assert property (
    RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) > $past(DINA, LAT))
      |-> DOUT == 32'd0
  );

  assert property (
    RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) == 32'd1)
      |-> DOUT == $past(DINA, LAT)
  );

  assert property (
    RST_N && $past(RST_N, LAT) && ($past(DINA, LAT) == 32'd0) && ($past(DINB, LAT) != 32'd0)
      |-> DOUT == 32'd0
  );

  // Reset behavior: output held at 0 in reset and for LAT cycles after release (pipeline flush)
  assert property (@(posedge CLK) !RST_N |-> DOUT == 32'd0);
  assert property (@(posedge CLK) $rose(RST_N) |=> (DOUT == 32'd0)[*LAT]);

  // Coverage
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) != 32'd0));                   // any valid divide
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINA, LAT) == 32'd0) && ($past(DINB, LAT) != 32'd0)); // 0/N
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) == 32'd1));                   // N/1
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) > $past(DINA, LAT)));         // N<D
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) == 32'hFFFF_FFFF));           // max denom
  cover property (RST_N && $past(RST_N, LAT) && ($past(DINB, LAT) == 32'd0));                   // divide-by-zero observed (behav unspecified)
endmodule

bind aq_div32x32 aq_div32x32_sva sva(.CLK(CLK), .RST_N(RST_N), .DINA(DINA), .DINB(DINB), .DOUT(DOUT));