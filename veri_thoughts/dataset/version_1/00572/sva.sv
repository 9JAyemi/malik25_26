// SVA for input_pipeline
// Bind this to the DUT to check reset, hold, shift, and end-to-end latency.

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
  input [WIDTH-1:0] pipeline_reg_11
);

  localparam int STAGES = 12;
  localparam int TOT    = WIDTH*STAGES;

  // Pack the pipeline for concise checks
  wire [TOT-1:0] stage_cat = {
    pipeline_reg_11, pipeline_reg_10, pipeline_reg_9,  pipeline_reg_8,
    pipeline_reg_7,  pipeline_reg_6,  pipeline_reg_5,  pipeline_reg_4,
    pipeline_reg_3,  pipeline_reg_2,  pipeline_reg_1,  pipeline_reg_0
  };

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Control must be known
  assert property (!$isunknown(clk_ena))
    else $error("clk_ena is X/Z at posedge clk");

  // Hold behavior: when disabled, all stages hold their values
  assert property ( !$past(reset) && !$past(clk_ena) |-> stage_cat == $past(stage_cat) )
    else $error("Pipeline changed while clk_ena was low");

  // Shift behavior: when enabled, pipeline shifts and stage0 captures previous in_stream
  assert property ( !$past(reset) && $past(clk_ena)
                    |-> stage_cat == { $past(stage_cat[TOT-1-WIDTH:0]), $past(in_stream) } )
    else $error("Pipeline shift/capture mismatch when clk_ena was high");

  // End-to-end latency: 12 consecutive enables move input to stage 11
  sequence en12; clk_ena[*STAGES]; endsequence
  assert property ( en12 |=> pipeline_reg_11 == $past(in_stream, STAGES) )
    else $error("End-to-end latency mismatch after 12 enables");

  // Asynchronous reset drives all stages to zero immediately
  assert property (@(posedge reset) ##0 (stage_cat == '0))
    else $error("Asynchronous reset did not clear pipeline to zero");

  // Coverage
  cover property (@(posedge reset) ##0 (stage_cat == '0));          // reset observed
  cover property (clk_ena);                                         // enable seen
  cover property (!clk_ena);                                        // stall seen
  cover property (en12 |=> pipeline_reg_11 == $past(in_stream, STAGES)); // full latency hit

endmodule

bind input_pipeline input_pipeline_sva #(.WIDTH(WIDTH)) u_input_pipeline_sva (.*);