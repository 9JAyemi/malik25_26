// SVA checker for rcn_filter
module rcn_filter_sva #(
  parameter logic [23:0] START_0 = 24'd1,
  parameter logic [23:0] END_0   = 24'd0,
  parameter logic [23:0] START_1 = 24'd1,
  parameter logic [23:0] END_1   = 24'd0,
  parameter logic [23:0] START_2 = 24'd1,
  parameter logic [23:0] END_2   = 24'd0,
  parameter logic [23:0] START_3 = 24'd1,
  parameter logic [23:0] END_3   = 24'd0
)(
  input  logic        clk,
  input  logic        rst,
  input  logic [68:0] rcn_in,
  input  logic [68:0] rcn_out,
  input  logic        filtered
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Previous-cycle address field used for filtering in DUT
  let addr_prev = $past(rcn_in[55:34]);

  // Per-window hits based on DUT semantics (inclusive ranges)
  let hit0 = (addr_prev >= START_0) && (addr_prev <= END_0);
  let hit1 = (addr_prev >= START_1) && (addr_prev <= END_1);
  let hit2 = (addr_prev >= START_2) && (addr_prev <= END_2);
  let hit3 = (addr_prev >= START_3) && (addr_prev <= END_3);
  let hit_any_prev = (hit0 || hit1 || hit2 || hit3);

  // Flag correctness: filtered reflects previous-cycle address window hit
  ap_flag: assert property (filtered == hit_any_prev);

  // Output gating correctness
  ap_zero_when_hit:     assert property (hit_any_prev  |-> (rcn_out == 69'd0));
  ap_pass_when_no_hit:  assert property (!hit_any_prev |-> (rcn_out == rcn_in));

  // Direct implications from flag
  ap_flag_implies_zero: assert property (filtered  |-> (rcn_out == 69'd0));
  ap_no_flag_passthru:  assert property (!filtered |-> (rcn_out == rcn_in));

  // Basic sanity (no X after reset release)
  ap_no_x_flag: assert property (!$isunknown(filtered));
  ap_no_x_out:  assert property (!$isunknown(rcn_out));

  // Reset behavior (asynchronous reset drives outputs low by next clk)
  ap_reset_clears: assert property (@(posedge clk) rst |-> (rcn_out == 69'd0 && filtered == 1'b0));

  // Coverage: hits and misses
  cp_hit_any:    cover property (hit_any_prev && filtered && (rcn_out == 69'd0));
  cp_no_hit:     cover property (!hit_any_prev && !filtered && (rcn_out == rcn_in));

  // Coverage: boundary hits for each window
  cp_b0_lo: cover property (($past(rcn_in[55:34]) == START_0) && filtered);
  cp_b0_hi: cover property (($past(rcn_in[55:34]) == END_0)   && filtered);
  cp_b1_lo: cover property (($past(rcn_in[55:34]) == START_1) && filtered);
  cp_b1_hi: cover property (($past(rcn_in[55:34]) == END_1)   && filtered);
  cp_b2_lo: cover property (($past(rcn_in[55:34]) == START_2) && filtered);
  cp_b2_hi: cover property (($past(rcn_in[55:34]) == END_2)   && filtered);
  cp_b3_lo: cover property (($past(rcn_in[55:34]) == START_3) && filtered);
  cp_b3_hi: cover property (($past(rcn_in[55:34]) == END_3)   && filtered);

  // Coverage: overlapping windows (examples)
  cp_overlap_01: cover property ((hit0 && hit1) && filtered && (rcn_out == 69'd0));
  cp_overlap_23: cover property ((hit2 && hit3) && filtered && (rcn_out == 69'd0));

endmodule

// Bind into DUT (example)
// bind rcn_filter rcn_filter_sva #(
//   .START_0(START_0), .END_0(END_0),
//   .START_1(START_1), .END_1(END_1),
//   .START_2(START_2), .END_2(END_2),
//   .START_3(START_3), .END_3(END_3)
// ) rcn_filter_sva_i (.*);