// SVA for sequence_detector
module sequence_detector_sva #(parameter [3:0] SEQ = 4'b1100) (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  in,
  input  logic [6:0]  seg_out,
  input  logic [3:0]  shift_reg,
  input  logic [3:0]  seq_detect,
  input  logic        detect
);
  default clocking cb @(posedge clk); endclocking

  // Reset state
  a_reset_state: assert property (reset |=> (shift_reg==4'b0 && seq_detect==4'b0 && detect==1'b0 && seg_out==7'b0000000));

  // State updates (as coded)
  a_shift_update:       assert property (!reset |=> shift_reg  == {in[0], $past(shift_reg)[3:1]});
  a_seq_detect_update:  assert property (!reset |=> seq_detect == in);

  // Detect set cause and stickiness
  a_detect_set_cause: assert property (disable iff (reset) $rose(detect) |-> $past(seq_detect)==SEQ);
  a_detect_latency:   assert property (disable iff (reset) $rose(detect) |-> $past(in)==SEQ);
  a_detect_sticky:    assert property (disable iff (reset) $past(detect) |-> detect);

  // Output mapping
  a_seg_out_map: assert property (seg_out == (detect ? 7'b0110000 : 7'b0000000));

  // No unknowns after reset
  a_no_x: assert property (disable iff (reset) !$isunknown({in, detect, seg_out, shift_reg, seq_detect}));

  // Coverage
  c_reset_seen:     cover property (reset);
  c_match_seen:     cover property (disable iff (reset) in==SEQ);
  c_detect_rose:    cover property (disable iff (reset) $rose(detect));
  c_seg_one:        cover property (disable iff (reset) detect && seg_out==7'b0110000);
  c_detect_sticky:  cover property (disable iff (reset) $rose(detect) ##1 detect ##1 detect);
endmodule

bind sequence_detector sequence_detector_sva #(.SEQ(4'b1100)) u_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .seg_out(seg_out),
  .shift_reg(shift_reg),
  .seq_detect(seq_detect),
  .detect(detect)
);