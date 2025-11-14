// SVA bind module for pipeline
module pipeline_sva #(parameter int WIDTH = 1) (
  input  logic                   clk,
  input  logic                   clk_ena,
  input  logic                   in_stream,
  input  logic                   reset,
  input  logic [WIDTH-1:0]       pipeline_reg_0,
  input  logic [WIDTH-1:0]       pipeline_reg_1,
  input  logic [WIDTH-1:0]       pipeline_reg_2,
  input  logic [WIDTH-1:0]       pipeline_reg_3,
  input  logic [WIDTH-1:0]       pipeline_reg_4,
  input  logic [WIDTH-1:0]       pipeline_reg_5,
  input  logic [WIDTH-1:0]       pipeline_reg_6,
  input  logic [WIDTH-1:0]       pipeline_reg_7,
  input  logic [WIDTH-1:0]       pipeline_reg_8,
  input  logic [WIDTH-1:0]       pipeline_reg_9,
  input  logic [WIDTH-1:0]       pipeline_reg_10,
  input  logic [WIDTH-1:0]       pipeline_reg_11,
  input  logic [WIDTH-1:0]       pipeline_reg_12,
  input  logic [WIDTH-1:0]       pipeline_reg_13
);

  // Collect stages for concise generate assertions
  logic [WIDTH-1:0] stage [0:13];
  always_comb begin
    stage[0]  = pipeline_reg_0;
    stage[1]  = pipeline_reg_1;
    stage[2]  = pipeline_reg_2;
    stage[3]  = pipeline_reg_3;
    stage[4]  = pipeline_reg_4;
    stage[5]  = pipeline_reg_5;
    stage[6]  = pipeline_reg_6;
    stage[7]  = pipeline_reg_7;
    stage[8]  = pipeline_reg_8;
    stage[9]  = pipeline_reg_9;
    stage[10] = pipeline_reg_10;
    stage[11] = pipeline_reg_11;
    stage[12] = pipeline_reg_12;
    stage[13] = pipeline_reg_13;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Async reset must clear immediately; also ensure zero on any clk while reset is high
  genvar r;
  for (r = 0; r < 14; r++) begin : g_reset
    // async clear in same time slot as posedge reset (after NBAs)
    ap_async_clear: assert property (@(posedge reset) disable iff (1'b0) ##0 (stage[r] == '0))
      else $error("pipeline: stage %0d not zero on async reset", r);

    // synchronous dominance of reset at clk edge
    ap_sync_clear:  assert property (reset |-> stage[r] == '0)
      else $error("pipeline: stage %0d not zero when reset sampled at clk", r);
  end

  // No X/Z on pipeline outputs outside reset
  genvar x;
  for (x = 0; x < 14; x++) begin : g_nox
    ap_no_x: assert property (!$isunknown(stage[x]))
      else $error("pipeline: stage %0d has X/Z", x);
  end

  // Hold behavior when clk_ena is low
  ap_hold_0: assert property (!clk_ena |-> $stable(stage[0]))
    else $error("pipeline: stage 0 changed while clk_ena=0");

  genvar h;
  for (h = 1; h < 14; h++) begin : g_hold
    ap_hold_i: assert property (!clk_ena |-> $stable(stage[h]))
      else $error("pipeline: stage %0d changed while clk_ena=0", h);
  end

  // Shift behavior when clk_ena is high
  ap_load0: assert property (clk_ena |-> stage[0] == $past(in_stream))
    else $error("pipeline: stage 0 did not sample in_stream on enable");

  genvar s;
  for (s = 1; s < 14; s++) begin : g_shift
    ap_shift_i: assert property (clk_ena |-> stage[s] == $past(stage[s-1]))
      else $error("pipeline: stage %0d did not sample stage %0d on enable", s, s-1);
  end

  // Coverage: reset seen, enable activity, and full-depth propagation under continuous enable
  cp_reset_event:  cover property (@(posedge reset) disable iff (1'b0) 1);
  cp_ena_toggle:   cover property (!clk_ena ##1 clk_ena ##1 !clk_ena);
  cp_full_latency: cover property (clk_ena [*14] ##0 (stage[13] == $past(in_stream,14)));

endmodule

// Bind into DUT
bind pipeline pipeline_sva #(.WIDTH(WIDTH)) u_pipeline_sva (.*);