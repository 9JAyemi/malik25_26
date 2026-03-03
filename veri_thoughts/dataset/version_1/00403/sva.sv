// Assertions for input_pipeline
// Bind this SVA module to the DUT
bind input_pipeline input_pipeline_sva #(.WIDTH(WIDTH)) u_input_pipeline_sva (.*);

module input_pipeline_sva #(parameter WIDTH=1) (input_pipeline dut);

  localparam int STAGES = 10;

  // Convenience concatenations
  wire [STAGES*WIDTH-1:0] regs_cat = { dut.pipeline_reg_9, dut.pipeline_reg_8, dut.pipeline_reg_7,
                                       dut.pipeline_reg_6, dut.pipeline_reg_5, dut.pipeline_reg_4,
                                       dut.pipeline_reg_3, dut.pipeline_reg_2, dut.pipeline_reg_1,
                                       dut.pipeline_reg_0 };

  wire [(STAGES-1)*WIDTH-1:0] upper_cat = { dut.pipeline_reg_9, dut.pipeline_reg_8, dut.pipeline_reg_7,
                                            dut.pipeline_reg_6, dut.pipeline_reg_5, dut.pipeline_reg_4,
                                            dut.pipeline_reg_3, dut.pipeline_reg_2, dut.pipeline_reg_1 };

  wire [(STAGES-1)*WIDTH-1:0] lower_cat = { dut.pipeline_reg_8, dut.pipeline_reg_7, dut.pipeline_reg_6,
                                            dut.pipeline_reg_5, dut.pipeline_reg_4, dut.pipeline_reg_3,
                                            dut.pipeline_reg_2, dut.pipeline_reg_1, dut.pipeline_reg_0 };

  default clocking cb @ (posedge dut.clk); endclocking
  default disable iff (dut.reset);

  // -------------------------
  // Reset behavior (async clear and hold at zero)
  // -------------------------
  // Async clear occurs immediately on posedge reset
  assert property (@(posedge dut.reset) regs_cat == '0)
    else $error("Async reset did not clear all pipeline registers to 0");

  // While reset is asserted, regs stay at zero on every clk edge
  assert property (dut.reset |-> regs_cat == '0)
    else $error("Pipeline registers not held at 0 while reset asserted");

  // -------------------------
  // Hold behavior when clk_ena is low
  // -------------------------
  assert property (!dut.clk_ena |=> regs_cat == $past(regs_cat))
    else $error("Registers changed while clk_ena=0");

  // -------------------------
  // Shift behavior when clk_ena is high (single-cycle next-state checks)
  // -------------------------
  assert property (dut.clk_ena |=> dut.pipeline_reg_0 == $past(dut.in_stream))
    else $error("pipeline_reg_0 did not capture in_stream on enable");

  assert property (dut.clk_ena |=> upper_cat == $past(lower_cat))
    else $error("Pipeline did not shift correctly on enable");

  // -------------------------
  // Multicycle latency checks for contiguous enables
  // reg_k equals in_stream delayed by k cycles when clk_ena is high for k cycles
  // -------------------------
  assert property (dut.clk_ena[*1] |=> dut.pipeline_reg_1 == $past(dut.in_stream,1))
    else $error("Latency-1 mismatch");
  assert property (dut.clk_ena[*2] |=> dut.pipeline_reg_2 == $past(dut.in_stream,2))
    else $error("Latency-2 mismatch");
  assert property (dut.clk_ena[*3] |=> dut.pipeline_reg_3 == $past(dut.in_stream,3))
    else $error("Latency-3 mismatch");
  assert property (dut.clk_ena[*4] |=> dut.pipeline_reg_4 == $past(dut.in_stream,4))
    else $error("Latency-4 mismatch");
  assert property (dut.clk_ena[*5] |=> dut.pipeline_reg_5 == $past(dut.in_stream,5))
    else $error("Latency-5 mismatch");
  assert property (dut.clk_ena[*6] |=> dut.pipeline_reg_6 == $past(dut.in_stream,6))
    else $error("Latency-6 mismatch");
  assert property (dut.clk_ena[*7] |=> dut.pipeline_reg_7 == $past(dut.in_stream,7))
    else $error("Latency-7 mismatch");
  assert property (dut.clk_ena[*8] |=> dut.pipeline_reg_8 == $past(dut.in_stream,8))
    else $error("Latency-8 mismatch");
  assert property (dut.clk_ena[*9] |=> dut.pipeline_reg_9 == $past(dut.in_stream,9))
    else $error("Latency-9 mismatch");

  // -------------------------
  // Sanity: no X/Z on key signals when not in reset
  // -------------------------
  assert property (!$isunknown({dut.clk_ena, dut.in_stream}))
    else $error("X/Z detected on clk_ena or in_stream");
  assert property (!$isunknown(regs_cat))
    else $error("X/Z detected on pipeline registers");

  // -------------------------
  // Coverage
  // -------------------------
  // Observe an enable burst long enough to push data across the whole pipe
  cover property (dut.clk_ena[*10]);

  // See reset, then release, then a shift
  cover property (@(posedge dut.clk) dut.reset ##1 !dut.reset ##1 dut.clk_ena);

  // Each stage updates at least once under enable
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_0));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_1));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_2));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_3));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_4));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_5));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_6));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_7));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_8));
  cover property (dut.clk_ena ##1 $changed(dut.pipeline_reg_9));

endmodule