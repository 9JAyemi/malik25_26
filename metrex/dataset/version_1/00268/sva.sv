// SVA for priority_encoder
// Bind this file to the DUT

module priority_encoder_sva (
  input logic        clk,
  input logic [3:0]  in,
  input logic [1:0]  out,
  input logic [1:0]  stage1_out,
  input logic [1:0]  stage2_out
);

  // helper: LSB-priority encoder
  function automatic logic [1:0] enc4_lsb_first (input logic [3:0] i);
    enc4_lsb_first = i[0] ? 2'd0 :
                     i[1] ? 2'd1 :
                     i[2] ? 2'd2 :
                     i[3] ? 2'd3 : 2'd0;
  endfunction

  // past-valid guard (no reset provided)
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Stage 2 must capture Stage 1 on each posedge
  a_stage2_captures_stage1: assert property (@(posedge clk)
      past_valid |-> stage2_out == $past(stage1_out)
  );

  // out must equal the register stage2_out
  a_out_is_stage2: assert property (@(posedge clk)
      out == stage2_out
  );

  // One-cycle latency functional check (when prior input had at least one 1)
  a_encode_function: assert property (@(posedge clk)
      past_valid && (|$past(in)) && !$isunknown($past(in))
      |-> out == enc4_lsb_first($past(in))
  );

  // No glitches between rising edges (out only changes on posedge)
  a_out_stable_between_rises: assert property (@(negedge clk) $stable(out));

  // No X on out when previous input was valid and known
  a_no_x_out_when_valid: assert property (@(posedge clk)
      past_valid && (|$past(in)) && !$isunknown($past(in))
      |-> !$isunknown(out)
  );

  // Stage1 should resolve to a known value whenever any input bit is 1
  a_stage1_known_when_any: assert property (@(posedge clk)
      (|in) && !$isunknown(in) |-> !$isunknown(stage1_out)
  );

  // Coverage: each priority winner
  c_in0: cover property (@(posedge clk) past_valid && $past(in)==4'b0001 && out==2'd0);
  c_in1: cover property (@(posedge clk) past_valid && $past(in)==4'b0010 && out==2'd1);
  c_in2: cover property (@(posedge clk) past_valid && $past(in)==4'b0100 && out==2'd2);
  c_in3: cover property (@(posedge clk) past_valid && $past(in)==4'b1000 && out==2'd3);

  // Coverage: multiple-bits-set, priority honored (lowest index wins)
  c_multi_1101: cover property (@(posedge clk) past_valid && $past(in)==4'b1101 && out==2'd0);
  c_multi_1010: cover property (@(posedge clk) past_valid && $past(in)==4'b1010 && out==2'd1);
  c_multi_0110: cover property (@(posedge clk) past_valid && $past(in)==4'b0110 && out==2'd1);
  c_multi_1111: cover property (@(posedge clk) past_valid && $past(in)==4'b1111 && out==2'd0);

  // Coverage: no bits set (exercises uncovered path in Stage 1)
  c_none_set: cover property (@(posedge clk) past_valid && $past(in)==4'b0000);

endmodule

// Bind into DUT
bind priority_encoder priority_encoder_sva u_priority_encoder_sva (
  .clk(clk),
  .in(in),
  .out(out),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out)
);