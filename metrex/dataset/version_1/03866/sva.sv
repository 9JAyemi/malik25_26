// SVA monitor for pipeline
module pipeline_sva (
  input clk,
  input reset,
  input clk_ena,
  input in_stream,
  input pipeline_reg_0,
  input pipeline_reg_1,
  input pipeline_reg_2,
  input pipeline_reg_3,
  input pipeline_reg_4,
  input pipeline_reg_5,
  input pipeline_reg_6,
  input pipeline_reg_7,
  input pipeline_reg_8,
  input pipeline_reg_9,
  input pipeline_reg_10,
  input pipeline_reg_11,
  input pipeline_reg_12,
  input pipeline_reg_13,
  input pipeline_reg_14,
  input pipeline_reg_15,
  input pipeline_reg_16
);
  // Vectorize for concise checks (p[0] = stage 0 ... p[16] = stage 16)
  wire [16:0] p = { pipeline_reg_16, pipeline_reg_15, pipeline_reg_14, pipeline_reg_13, pipeline_reg_12,
                    pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,  pipeline_reg_8,  pipeline_reg_7,
                    pipeline_reg_6,  pipeline_reg_5,  pipeline_reg_4,  pipeline_reg_3,  pipeline_reg_2,
                    pipeline_reg_1,  pipeline_reg_0 };

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset dominates (checked in same cycle with ##0)
  assert property (@cb reset |-> ##0 (p == '0));

  // Hold when disabled
  assert property (@cb disable iff (reset) !clk_ena |-> ##0 (p == $past(p)));

  // Shift when enabled (one-step local behavior)
  assert property (@cb disable iff (reset)
                   clk_ena |-> ##0 (p[16:1] == $past(p[15:0]) && p[0] == $past(in_stream)));

  // End-to-end latency across i+1 consecutive enables
  genvar i;
  generate
    for (i = 0; i <= 16; i++) begin : LAT
      assert property (@cb disable iff (reset)
                       (clk_ena [* (i+1)]) |-> ##0 (p[i] == $past(in_stream, i+1)));
    end
  endgenerate

  // No X/Z on pipeline after reset is released
  assert property (@cb (!reset && $past(!reset)) |-> !$isunknown(p));

  // Coverage: full pipeline fill with 1's on consecutive enables reaching last stage
  cover property (@cb disable iff (reset) (clk_ena && in_stream)[*17] ##0 (p[16] == 1'b1));

  // Coverage: observe hold then shift
  cover property (@cb disable iff (reset) (!clk_ena)[*3] ##1 clk_ena);

  // Coverage: enable toggling patterns
  cover property (@cb disable iff (reset) clk_ena ##1 !clk_ena ##1 clk_ena);
endmodule

// Bind into DUT
bind pipeline pipeline_sva u_pipeline_sva (
  .clk(clk),
  .reset(reset),
  .clk_ena(clk_ena),
  .in_stream(in_stream),
  .pipeline_reg_0(pipeline_reg_0),
  .pipeline_reg_1(pipeline_reg_1),
  .pipeline_reg_2(pipeline_reg_2),
  .pipeline_reg_3(pipeline_reg_3),
  .pipeline_reg_4(pipeline_reg_4),
  .pipeline_reg_5(pipeline_reg_5),
  .pipeline_reg_6(pipeline_reg_6),
  .pipeline_reg_7(pipeline_reg_7),
  .pipeline_reg_8(pipeline_reg_8),
  .pipeline_reg_9(pipeline_reg_9),
  .pipeline_reg_10(pipeline_reg_10),
  .pipeline_reg_11(pipeline_reg_11),
  .pipeline_reg_12(pipeline_reg_12),
  .pipeline_reg_13(pipeline_reg_13),
  .pipeline_reg_14(pipeline_reg_14),
  .pipeline_reg_15(pipeline_reg_15),
  .pipeline_reg_16(pipeline_reg_16)
);