// SVA for input_pipeline
// Bindable, concise, and covers reset, hold, shift, and end-to-end behavior.

module input_pipeline_sva #(parameter WIDTH=1) (
  input clk,
  input reset,
  input clk_ena,
  input [WIDTH-1:0] in_stream,
  input [WIDTH-1:0] pipeline_reg_0,
  input [WIDTH-1:0] pipeline_reg_1,
  input [WIDTH-1:0] pipeline_reg_2,
  input [WIDTH-1:0] pipeline_reg_3,
  input [WIDTH-1:0] pipeline_reg_4,
  input [WIDTH-1:0] pipeline_reg_5,
  input [WIDTH-1:0] pipeline_reg_6,
  input [WIDTH-1:0] pipeline_reg_7,
  input [WIDTH-1:0] pipeline_reg_8,
  input [WIDTH-1:0] pipeline_reg_9,
  input [WIDTH-1:0] pipeline_reg_10,
  input [WIDTH-1:0] pipeline_reg_11,
  input [WIDTH-1:0] pipeline_reg_12,
  input [WIDTH-1:0] pipeline_reg_13,
  input [WIDTH-1:0] pipeline_reg_14,
  input [WIDTH-1:0] pipeline_reg_15,
  input [WIDTH-1:0] pipeline_reg_16,
  input [WIDTH-1:0] pipeline_reg_17,
  input [WIDTH-1:0] pipeline_reg_18,
  input [WIDTH-1:0] pipeline_reg_19,
  input [WIDTH-1:0] pipeline_reg_20,
  input [WIDTH-1:0] pipeline_reg_21,
  input [WIDTH-1:0] pipeline_reg_22,
  input [WIDTH-1:0] pipeline_reg_23
);

  localparam int DEPTH = 24;

  // Packed vectors for concise assertions
  wire [WIDTH*DEPTH-1:0] regs_cat = {
    pipeline_reg_23, pipeline_reg_22, pipeline_reg_21, pipeline_reg_20,
    pipeline_reg_19, pipeline_reg_18, pipeline_reg_17, pipeline_reg_16,
    pipeline_reg_15, pipeline_reg_14, pipeline_reg_13, pipeline_reg_12,
    pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,  pipeline_reg_8,
    pipeline_reg_7,  pipeline_reg_6,  pipeline_reg_5,  pipeline_reg_4,
    pipeline_reg_3,  pipeline_reg_2,  pipeline_reg_1,  pipeline_reg_0
  };

  wire [WIDTH*DEPTH-1:0] shift_src = {
    pipeline_reg_22, pipeline_reg_21, pipeline_reg_20,
    pipeline_reg_19, pipeline_reg_18, pipeline_reg_17, pipeline_reg_16,
    pipeline_reg_15, pipeline_reg_14, pipeline_reg_13, pipeline_reg_12,
    pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,  pipeline_reg_8,
    pipeline_reg_7,  pipeline_reg_6,  pipeline_reg_5,  pipeline_reg_4,
    pipeline_reg_3,  pipeline_reg_2,  pipeline_reg_1,  pipeline_reg_0,
    in_stream
  };

  // Reset: async clear to 0, observed both at clk edge and reset edge.
  assert property (@(posedge clk) reset |-> regs_cat == '0)
    else $error("Pipeline not zero during reset at clk edge");

  // Use ##0 to sample after NBA updates on posedge reset
  assert property (@(posedge reset) ##0 (regs_cat == '0))
    else $error("Pipeline not cleared to zero on async reset");

  // Hold when disabled
  assert property (@(posedge clk) disable iff (reset)
                   !clk_ena |-> $stable(regs_cat))
    else $error("Pipeline changed without clk_ena");

  // Single-cycle shift behavior when enabled (vector form)
  assert property (@(posedge clk) disable iff (reset)
                   clk_ena |-> regs_cat == $past(shift_src))
    else $error("Pipeline shift mismatch on enabled cycle");

  // End-to-end latency under 24 consecutive enables
  assert property (@(posedge clk) disable iff (reset)
                   clk_ena[*24] |-> pipeline_reg_23 == $past(in_stream,24))
    else $error("End-to-end latency mismatch after 24 enables");

  // Minimal functional coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) $fell(reset));
  cover property (@(posedge clk) disable iff (reset) !clk_ena);
  cover property (@(posedge clk) disable iff (reset) clk_ena[*24]
                  ##1 (pipeline_reg_23 == $past(in_stream,24)));

endmodule

// Bind into the DUT
bind input_pipeline input_pipeline_sva #(.WIDTH(WIDTH)) input_pipeline_sva_i (.*);