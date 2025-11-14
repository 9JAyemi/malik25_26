// SVA for mig_7series_v2_3_poc_meta
module mig_7series_v2_3_poc_meta_sva #(
  parameter SCANFROMRIGHT   = 0,
  parameter TAPCNTRWIDTH    = 7,
  parameter TAPSPERKCLK     = 112
)(
  // DUT clock/reset and IOs
  input logic                        clk,
  input logic                        rst,
  input logic                        mmcm_edge_detect_rdy,
  input logic                        run_end,
  input logic                        run_polarity,
  input logic [1:0]                  ninety_offsets,
  input logic                        use_noise_window,
  input logic [TAPCNTRWIDTH-1:0]     rise_lead_right,
  input logic [TAPCNTRWIDTH-1:0]     rise_trail_left,
  input logic [TAPCNTRWIDTH-1:0]     rise_lead_center,
  input logic [TAPCNTRWIDTH-1:0]     rise_trail_center,
  input logic [TAPCNTRWIDTH-1:0]     rise_trail_right,
  input logic [TAPCNTRWIDTH-1:0]     rise_lead_left,
  input logic                        ktap_at_right_edge,
  input logic                        ktap_at_left_edge,
  input logic                        mmcm_lbclk_edge_aligned,
  input logic                        mmcm_edge_detect_done,
  input logic                        poc_backup,

  // Internals used for checking
  input logic                        run_end_r,
  input logic                        run_end_r1,
  input logic                        run_end_r2,
  input logic                        run_end_r3,
  input logic                        run_polarity_held_r,
  input logic [1:0]                  run_ends_r,
  input logic                        done_r,
  input logic [TAPCNTRWIDTH-1:0]     rise_lead_center_offset_r,
  input logic [TAPCNTRWIDTH-1:0]     rise_trail_center_offset_r,
  input logic [TAPCNTRWIDTH-1:0]     edge_diff_r,
  input logic [TAPCNTRWIDTH:0]       edge_center_r,
  input logic [TAPCNTRWIDTH-1:0]     center_diff_r,
  input logic [TAPCNTRWIDTH:0]       window_center_r,
  input logic [TAPCNTRWIDTH+1:0]     diff_r,
  input logic [TAPCNTRWIDTH+1:0]     abs_diff,
  input logic [TAPCNTRWIDTH+1:0]     prev_r,
  input logic                        diffs_eq_r
);

  default clocking cb @(posedge clk); endclocking

  // Golden helper functions (mirror DUT math)
  localparam int NINETY = TAPSPERKCLK/4;
  function automatic logic [TAPCNTRWIDTH-1:0] f_offset(
    input logic [TAPCNTRWIDTH-1:0] a, input logic [1:0] b, input int base);
    int ii;
    begin
      ii = (a + b*NINETY) < base ? (a + b*NINETY) : (a + b*NINETY - base);
      f_offset = ii[TAPCNTRWIDTH-1:0];
    end
  endfunction

  function automatic logic [TAPCNTRWIDTH-1:0] f_mod_sub(
    input logic [TAPCNTRWIDTH-1:0] a, input logic [TAPCNTRWIDTH-1:0] b, input int base);
    begin
      f_mod_sub = (a>=b) ? a-b : a+base-b;
    end
  endfunction

  function automatic logic [TAPCNTRWIDTH:0] f_center(
    input logic [TAPCNTRWIDTH-1:0] left, input logic [TAPCNTRWIDTH-1:0] diff, input int base);
    int ci;
    begin
      ci = ({left,1'b0} + diff < base*2) ? ({left,1'b0} + diff) : ({left,1'b0} + diff - base*2);
      f_center = ci[TAPCNTRWIDTH:0];
    end
  endfunction

  // Common lets
  let reset_run_ends = rst || !mmcm_edge_detect_rdy;
  let offs_exp       = (SCANFROMRIGHT==1) ? ninety_offsets : (2'b00 - ninety_offsets);
  let left_exp       = use_noise_window ? rise_lead_left  : rise_trail_left;
  let right_exp      = use_noise_window ? rise_trail_right: rise_lead_right;
  let done_ns_exp    = mmcm_edge_detect_rdy && &run_ends_r;
  let centering      = !(ktap_at_right_edge || ktap_at_left_edge);
  let indicate_align = (!rst) && centering && done_ns_exp;

  // 1) Run/polarity and run_ends behavior
  // reset forces run_ends_r to zero next cycle
  a_run_ends_reset: assert property (reset_run_ends |=> run_ends_r==2'b00);

  // run_polarity is captured on run_end
  a_polarity_cap: assert property (disable iff (rst) run_end |=> run_polarity_held_r == $past(run_polarity));

  // run_ends increment sequence (00->01 gated by polarity, then ->10 ->11), saturate at 11
  a_re0_to_1: assert property (disable iff (rst)
    ($past(run_ends_r)==2'b00 && $past(run_end_r3 && run_polarity_held_r) && !$past(reset_run_ends)) |=> run_ends_r==2'b01);

  a_re1_to_2: assert property (disable iff (rst)
    ($past(run_ends_r)==2'b01 && $past(run_end_r3) && !$past(reset_run_ends)) |=> run_ends_r==2'b10);

  a_re2_to_3: assert property (disable iff (rst)
    ($past(run_ends_r)==2'b10 && $past(run_end_r3) && !$past(reset_run_ends)) |=> run_ends_r==2'b11);

  a_re_hold_3: assert property (disable iff (rst)
    ($past(run_ends_r)==2'b11 && !$past(reset_run_ends)) |=> run_ends_r==2'b11);

  // done output is registered version of (rdy && &run_ends_r)
  a_done_pipe: assert property (disable iff (rst)
    mmcm_edge_detect_done == $past(mmcm_edge_detect_rdy && &run_ends_r));

  // 2) Offset/diff/center pipeline math
  a_lead_off: assert property (disable iff (rst)
    rise_lead_center_offset_r  == f_offset($past(rise_lead_center),  $past(offs_exp), TAPSPERKCLK));
  a_trail_off: assert property (disable iff (rst)
    rise_trail_center_offset_r == f_offset($past(rise_trail_center), $past(offs_exp), TAPSPERKCLK));

  a_edge_diff: assert property (disable iff (rst)
    edge_diff_r == f_mod_sub($past(rise_trail_center_offset_r), $past(rise_lead_center_offset_r), TAPSPERKCLK));

  a_edge_center: assert property (disable iff (rst)
    edge_center_r == f_center($past(rise_lead_center_offset_r), $past(edge_diff_r), TAPSPERKCLK));

  a_center_diff: assert property (disable iff (rst)
    center_diff_r == f_mod_sub($past(right_exp), $past(left_exp), TAPSPERKCLK));

  a_window_center: assert property (disable iff (rst)
    window_center_r == f_center($past(left_exp), $past(center_diff_r), TAPSPERKCLK));

  // diff_r from centers (mod 2*BASE)
  a_diff: assert property (disable iff (rst)
  begin
    logic [TAPCNTRWIDTH+1:0] l = {1'b0, (SCANFROMRIGHT==1) ? $past(window_center_r) : $past(edge_center_r)};
    logic [TAPCNTRWIDTH+1:0] r = {1'b0, (SCANFROMRIGHT==1) ? $past(edge_center_r)   : $past(window_center_r)};
    diff_r == ((r>=l) ? (r-l) : (r + (TAPSPERKCLK*2) - l));
  end);

  // abs_diff must be min distance on 2*BASE ring
  a_absdiff: assert property (disable iff (rst)
    abs_diff == ((diff_r > TAPSPERKCLK) ? (TAPSPERKCLK*2 - diff_r) : diff_r));

  // 3) prev_r update when done_ns is true
  a_prev_update: assert property (disable iff (rst)
    prev_r == ($past(done_ns_exp) ? $past(diff_r) : $past(prev_r)));

  // 4) Alignment and backup signals
  // edge-aligned is registered version of indicate_align && (zero diff OR falling diffs_eq)
  let diffs_eq_comb = (abs_diff == diff_r);
  a_aligned: assert property (disable iff (rst)
    mmcm_lbclk_edge_aligned ==
      $past(indicate_align && ((~|diff_r) || (!diffs_eq_comb && diffs_eq_r))));

  // aligned implies centering and done were true in the cycle before it asserted
  a_aligned_ctx: assert property (disable iff (rst)
    mmcm_lbclk_edge_aligned |-> ($past(centering) && $past(done_ns_exp)));

  // poc_backup asserts when aligned_ns and abs_diff increased vs prev_r
  a_backup: assert property (disable iff (rst)
    poc_backup == ($past(indicate_align && ((~|diff_r) || (!diffs_eq_comb && diffs_eq_r))) &&
                   ($past(abs_diff) > $past(prev_r))));

  // 5) Minimal functional coverage
  c_done:      cover property ($rose(mmcm_edge_detect_done));
  c_align0:    cover property ($rose(mmcm_lbclk_edge_aligned) && $past(~|diff_r));
  c_alignFall: cover property ($rose(mmcm_lbclk_edge_aligned) && $past(diffs_eq_r) && !$past(diffs_eq_comb));
  c_backup:    cover property ($rose(poc_backup));

endmodule

// Bind into the DUT
bind mig_7series_v2_3_poc_meta
  mig_7series_v2_3_poc_meta_sva #(
    .SCANFROMRIGHT(SCANFROMRIGHT),
    .TAPCNTRWIDTH (TAPCNTRWIDTH),
    .TAPSPERKCLK  (TAPSPERKCLK)
  ) poc_meta_sva_i (.*);