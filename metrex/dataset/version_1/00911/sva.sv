// SVA checker for mig_7series_v2_3_ddr_phy_wrlvl_off_delay
// Bind this checker to the DUT; asserts and covers key behaviors concisely.

module mig_7series_v2_3_ddr_phy_wrlvl_off_delay_sva #(
  parameter int PO_INITIAL_DLY = 46,
  parameter int TDQSS_DLY      = 1,
  parameter int DQS_CNT_WIDTH  = 3
)(
  input  logic                       clk,
  input  logic                       rst,
  // inputs/pipes
  input  logic                       cmd_delay_start,
  input  logic                       cmd_delay_start_r1,
  input  logic                       cmd_delay_start_r2,
  input  logic                       cmd_delay_start_r3,
  input  logic                       cmd_delay_start_r4,
  input  logic                       cmd_delay_start_r5,
  input  logic                       cmd_delay_start_r6,
  input  logic                       pi_fine_dly_dec_done,
  input  logic                       pi_fine_dly_dec_done_r,
  // f-path
  input  logic [5:0]                 po_delay_cnt_r,
  input  logic                       po_en_stg2_f,
  input  logic                       po_stg2_f_incdec,
  input  logic [DQS_CNT_WIDTH:0]     lane_cnt_po_r,
  input  logic                       po_delay_done,
  input  logic                       po_delay_done_r1,
  input  logic                       po_delay_done_r2,
  input  logic                       po_delay_done_r3,
  input  logic                       po_delay_done_r4,
  // c-path
  input  logic [5:0]                 delay_cnt_r,
  input  logic                       po_en_stg2_c,
  input  logic                       po_stg2_incdec_c,
  input  logic [DQS_CNT_WIDTH:0]     lane_cnt_dqs_c_r,
  input  logic                       delay_done,
  input  logic                       delay_done_r1,
  input  logic                       delay_done_r2,
  input  logic                       delay_done_r3,
  input  logic                       delay_done_r4,
  // outputs
  input  logic                       phy_ctl_rdy_dly,
  input  logic                       po_dec_done,
  input  logic                       po_ck_addr_cmd_delay_done,
  input  logic                       po_s2_incdec_f,
  input  logic                       po_en_s2_f,
  input  logic                       po_s2_incdec_c,
  input  logic                       po_en_s2_c,
  input  logic [DQS_CNT_WIDTH:0]     ctl_lane_cnt
);

  default clocking cb @(posedge clk); endclocking

  // Simple pipe checks
  assert property (disable iff (rst) cmd_delay_start_r1 == $past(cmd_delay_start));
  assert property (disable iff (rst) cmd_delay_start_r2 == $past(cmd_delay_start_r1));
  assert property (disable iff (rst) cmd_delay_start_r3 == $past(cmd_delay_start_r2));
  assert property (disable iff (rst) cmd_delay_start_r4 == $past(cmd_delay_start_r3));
  assert property (disable iff (rst) cmd_delay_start_r5 == $past(cmd_delay_start_r4));
  assert property (disable iff (rst) cmd_delay_start_r6 == $past(cmd_delay_start_r5));
  assert property (disable iff (rst) pi_fine_dly_dec_done_r == $past(pi_fine_dly_dec_done));

  // Output wires mirror internal regs
  assert property (po_s2_incdec_f == po_stg2_f_incdec);
  assert property (po_en_s2_f     == po_en_stg2_f);
  assert property (po_s2_incdec_c == po_stg2_incdec_c);
  assert property (po_en_s2_c     == po_en_stg2_c);
  assert property (ctl_lane_cnt   == lane_cnt_dqs_c_r);

  // Ready indication
  assert property (phy_ctl_rdy_dly == cmd_delay_start_r6);

  // po_dec_done mapping
  generate
    if (PO_INITIAL_DLY == 0) begin
      assert property (po_dec_done == 1'b1);
    end else begin
      assert property (po_dec_done == po_delay_done_r4);
    end
  endgenerate

  // po_ck_addr_cmd_delay_done mapping
  generate
    if (TDQSS_DLY == 0) begin
      assert property (po_ck_addr_cmd_delay_done == pi_fine_dly_dec_done_r);
    end else begin
      assert property (po_ck_addr_cmd_delay_done == delay_done_r4);
    end
  endgenerate

  // f-path control behavior
  assert property ((rst || !cmd_delay_start_r6 || po_delay_done) |=> (po_en_stg2_f == 1'b0 && po_stg2_f_incdec == 1'b0));
  // po_stg2_f_incdec is constant 0
  assert property (po_stg2_f_incdec == 1'b0);
  // Toggle enable when active and counting
  assert property (disable iff (rst)
                   (cmd_delay_start_r6 && !po_delay_done && (po_delay_cnt_r > 0) && $past(cmd_delay_start_r6 && !po_delay_done && (po_delay_cnt_r > 0)))
                   |-> (po_en_stg2_f != $past(po_en_stg2_f)));
  // Counter load/decrement/hold
  generate if (PO_INITIAL_DLY >= 31) begin
    assert property ((rst || !cmd_delay_start_r6 || (po_delay_cnt_r == 6'd0)) |=> po_delay_cnt_r == (PO_INITIAL_DLY - 31));
  end endgenerate
  assert property ((po_en_stg2_f && (po_delay_cnt_r > 6'd0)) |=> po_delay_cnt_r == $past(po_delay_cnt_r) - 1);
  assert property (disable iff (rst)
                   (!po_en_stg2_f && cmd_delay_start_r6 && (po_delay_cnt_r > 6'd0)) |=> po_delay_cnt_r == $past(po_delay_cnt_r));
  // Lane count update
  assert property (rst |=> lane_cnt_po_r == '0);
  assert property ((po_en_stg2_f && (po_delay_cnt_r == 6'd1)) |=> lane_cnt_po_r == $past(lane_cnt_po_r) + 1);
  assert property (disable iff (rst)
                   !(po_en_stg2_f && (po_delay_cnt_r == 6'd1)) |=> lane_cnt_po_r == $past(lane_cnt_po_r));
  // Done set/clear and pipe
  assert property ((rst || !cmd_delay_start_r6) |=> po_delay_done == 1'b0);
  assert property (((po_delay_cnt_r == 6'd1) && (lane_cnt_po_r == '0)) |=> po_delay_done == 1'b1);
  assert property (disable iff (rst) (po_delay_done && cmd_delay_start_r6) |=> po_delay_done);
  assert property (disable iff (rst) po_delay_done_r1 == $past(po_delay_done));
  assert property (disable iff (rst) po_delay_done_r2 == $past(po_delay_done_r1));
  assert property (disable iff (rst) po_delay_done_r3 == $past(po_delay_done_r2));
  assert property (disable iff (rst) po_delay_done_r4 == $past(po_delay_done_r3));

  // c-path control behavior
  assert property ((rst || !pi_fine_dly_dec_done_r || delay_done) |=> (po_en_stg2_c == 1'b0 && po_stg2_incdec_c == 1'b1));
  // Toggle enable when active and counting
  assert property (disable iff (rst)
                   (pi_fine_dly_dec_done_r && !delay_done && (delay_cnt_r > 0) && $past(pi_fine_dly_dec_done_r && !delay_done && (delay_cnt_r > 0)))
                   |-> (po_en_stg2_c != $past(po_en_stg2_c)));
  // Counter load/decrement/hold
  assert property ((rst || !pi_fine_dly_dec_done_r || (delay_cnt_r == 6'd0)) |=> delay_cnt_r == TDQSS_DLY[5:0]);
  assert property ((po_en_stg2_c && (delay_cnt_r > 6'd0)) |=> delay_cnt_r == $past(delay_cnt_r) - 1);
  assert property (disable iff (rst)
                   (!po_en_stg2_c && pi_fine_dly_dec_done_r && (delay_cnt_r > 6'd0)) |=> delay_cnt_r == $past(delay_cnt_r));
  // Lane count update
  assert property (rst |=> lane_cnt_dqs_c_r == '0);
  assert property ((po_en_stg2_c && (delay_cnt_r == 6'd1)) |=> lane_cnt_dqs_c_r == $past(lane_cnt_dqs_c_r) + 1);
  assert property (disable iff (rst)
                   !(po_en_stg2_c && (delay_cnt_r == 6'd1)) |=> lane_cnt_dqs_c_r == $past(lane_cnt_dqs_c_r));
  // Done set/clear and pipe
  assert property ((rst || !pi_fine_dly_dec_done_r) |=> delay_done == 1'b0);
  assert property (((delay_cnt_r == 6'd1) && (lane_cnt_dqs_c_r == '0)) |=> delay_done == 1'b1);
  assert property (disable iff (rst) (delay_done && pi_fine_dly_dec_done_r) |=> delay_done);
  assert property (disable iff (rst) delay_done_r1 == $past(delay_done));
  assert property (disable iff (rst) delay_done_r2 == $past(delay_done_r1));
  assert property (disable iff (rst) delay_done_r3 == $past(delay_done_r2));
  assert property (disable iff (rst) delay_done_r4 == $past(delay_done_r3));

  // Covers: exercise both paths and observable outputs
  cover property (disable iff (rst)
                  cmd_delay_start ##1 cmd_delay_start_r6 ##[1:$] po_delay_done ##1 po_dec_done);
  cover property (disable iff (rst)
                  pi_fine_dly_dec_done ##1 pi_fine_dly_dec_done_r ##[1:$] delay_done ##1 po_ck_addr_cmd_delay_done);
  cover property (disable iff (rst)
                  (cmd_delay_start_r6 && (po_delay_cnt_r > 0)) ##1 (po_en_stg2_f != $past(po_en_stg2_f)) ##1 (po_en_stg2_f != $past(po_en_stg2_f)));
  cover property (disable iff (rst)
                  (pi_fine_dly_dec_done_r && (delay_cnt_r > 0)) ##1 (po_en_stg2_c != $past(po_en_stg2_c)) ##1 (po_en_stg2_c != $past(po_en_stg2_c)));

endmodule


// Bind to all instances of the DUT; connect to internal signals in the DUT scope.
bind mig_7series_v2_3_ddr_phy_wrlvl_off_delay
  mig_7series_v2_3_ddr_phy_wrlvl_off_delay_sva #(
    .PO_INITIAL_DLY(PO_INITIAL_DLY),
    .TDQSS_DLY(TDQSS_DLY),
    .DQS_CNT_WIDTH(DQS_CNT_WIDTH)
  ) i_mig_7series_v2_3_ddr_phy_wrlvl_off_delay_sva (
    .clk                     (clk),
    .rst                     (rst),
    .cmd_delay_start         (cmd_delay_start),
    .cmd_delay_start_r1      (cmd_delay_start_r1),
    .cmd_delay_start_r2      (cmd_delay_start_r2),
    .cmd_delay_start_r3      (cmd_delay_start_r3),
    .cmd_delay_start_r4      (cmd_delay_start_r4),
    .cmd_delay_start_r5      (cmd_delay_start_r5),
    .cmd_delay_start_r6      (cmd_delay_start_r6),
    .pi_fine_dly_dec_done    (pi_fine_dly_dec_done),
    .pi_fine_dly_dec_done_r  (pi_fine_dly_dec_done_r),
    .po_delay_cnt_r          (po_delay_cnt_r),
    .po_en_stg2_f            (po_en_stg2_f),
    .po_stg2_f_incdec        (po_stg2_f_incdec),
    .lane_cnt_po_r           (lane_cnt_po_r),
    .po_delay_done           (po_delay_done),
    .po_delay_done_r1        (po_delay_done_r1),
    .po_delay_done_r2        (po_delay_done_r2),
    .po_delay_done_r3        (po_delay_done_r3),
    .po_delay_done_r4        (po_delay_done_r4),
    .delay_cnt_r             (delay_cnt_r),
    .po_en_stg2_c            (po_en_stg2_c),
    .po_stg2_incdec_c        (po_stg2_incdec_c),
    .lane_cnt_dqs_c_r        (lane_cnt_dqs_c_r),
    .delay_done              (delay_done),
    .delay_done_r1           (delay_done_r1),
    .delay_done_r2           (delay_done_r2),
    .delay_done_r3           (delay_done_r3),
    .delay_done_r4           (delay_done_r4),
    .phy_ctl_rdy_dly         (phy_ctl_rdy_dly),
    .po_dec_done             (po_dec_done),
    .po_ck_addr_cmd_delay_done(po_ck_addr_cmd_delay_done),
    .po_s2_incdec_f          (po_s2_incdec_f),
    .po_en_s2_f              (po_en_s2_f),
    .po_s2_incdec_c          (po_s2_incdec_c),
    .po_en_s2_c              (po_en_s2_c),
    .ctl_lane_cnt            (ctl_lane_cnt)
  );