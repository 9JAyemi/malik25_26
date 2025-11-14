// SVA for ir_rcv
`ifndef IR_RCV_SVA
`define IR_RCV_SVA

bind ir_rcv ir_rcv_sva();

module ir_rcv_sva;

  // mirror state encodings locally
  localparam [1:0] STATE_IDLE       = 2'b00;
  localparam [1:0] STATE_LEADVERIFY = 2'b01;
  localparam [1:0] STATE_DATARCV    = 2'b10;

  default clocking cb @(posedge clk50); endclocking
  default disable iff (!reset_n);

  // Reset post-conditions
  assert property ($rose(reset_n) |-> (state == STATE_IDLE &&
                                       act_cnt == 0 && leadvrf_cnt == 0 && datarcv_cnt == 0 &&
                                       bits_detected == 0 && databuf == 32'h0 &&
                                       rpt_cnt == 0 && ir_code == 32'h0 && ir_code_ack == 1'b0));

  // State legality
  assert property (state inside {STATE_IDLE, STATE_LEADVERIFY, STATE_DATARCV});

  // act_cnt
  assert property ($past(reset_n) && $past(state == STATE_IDLE && !ir_rx) |-> act_cnt == $past(act_cnt)+1);
  assert property ($past(reset_n) && !$past(state == STATE_IDLE && !ir_rx) |-> act_cnt == 0);

  // leadvrf_cnt
  assert property ($past(reset_n) && $past(state == STATE_LEADVERIFY && ir_rx) |-> leadvrf_cnt == $past(leadvrf_cnt)+1);
  assert property ($past(reset_n) && !$past(state == STATE_LEADVERIFY && ir_rx) |-> leadvrf_cnt == 0);

  // datarcv_cnt
  assert property ($past(reset_n) && $past(state == STATE_DATARCV && ir_rx) |-> datarcv_cnt == $past(datarcv_cnt)+1);
  assert property ($past(reset_n) && !$past(state == STATE_DATARCV && ir_rx) |-> datarcv_cnt == 0);

  // bits_detected
  assert property ($past(reset_n) && $past(state == STATE_DATARCV && datarcv_cnt == BIT_DETECT_THOLD) |-> bits_detected == $past(bits_detected)+1);
  assert property ($past(state == STATE_DATARCV && datarcv_cnt != BIT_DETECT_THOLD) |-> bits_detected == $past(bits_detected));
  assert property ($past(state != STATE_DATARCV) |-> bits_detected == 0);

  // databuf: only 0->1 at BIT_ONE_THOLD, no 1->0 during DATARCV, zeroed otherwise
  genvar i;
  generate
    for (i=0; i<32; i++) begin : g_db
      assert property ($rose(databuf[i]) |-> $past(state == STATE_DATARCV && datarcv_cnt == BIT_ONE_THOLD && (i == 32 - $past(bits_detected))));
      assert property ($fell(databuf[i]) |-> state != STATE_DATARCV);
    end
  endgenerate
  assert property ($past(state == STATE_DATARCV) && state == STATE_DATARCV |-> (($past(databuf) & ~databuf) == 0));
  assert property (state != STATE_DATARCV |-> databuf == 32'h0);

  // Index validity when writing a '1'
  assert property (state == STATE_DATARCV && datarcv_cnt == BIT_ONE_THOLD |-> (bits_detected >= 1 && bits_detected <= 32));

  // State transitions and stability
  assert property (state == STATE_IDLE && act_cnt >= LEADCODE_LO_THOLD |=> state == STATE_LEADVERIFY);
  assert property (state == STATE_IDLE && act_cnt <  LEADCODE_LO_THOLD |=> state == STATE_IDLE);

  assert property (state == STATE_LEADVERIFY && leadvrf_cnt >= LEADCODE_HI_THOLD |=> state == STATE_DATARCV);
  assert property (state == STATE_LEADVERIFY && leadvrf_cnt <  LEADCODE_HI_THOLD |=> state == STATE_LEADVERIFY);

  assert property (state == STATE_DATARCV && (datarcv_cnt >= IDLE_THOLD || bits_detected >= 33) |=> state == STATE_IDLE);
  assert property (state == STATE_DATARCV && (datarcv_cnt < IDLE_THOLD && bits_detected < 33) |=> state == STATE_DATARCV);

  // rpt_cnt: increment and reset-on-repeat-mark
  assert property ($past(reset_n) && $past(!(state == STATE_LEADVERIFY && leadvrf_cnt == LEADCODE_HI_RPT_THOLD)) |-> rpt_cnt == $past(rpt_cnt)+1);
  assert property ($past(state == STATE_LEADVERIFY && leadvrf_cnt == LEADCODE_HI_RPT_THOLD) |-> rpt_cnt == 0);

  // Ack/Code rules
  assert property (ir_code_ack |-> (state == STATE_DATARCV && bits_detected == 32 &&
                                    (databuf[15:8] == ~databuf[7:0]) && ir_code == databuf));
  assert property ((bits_detected == 32 && (databuf[15:8] == ~databuf[7:0])) |-> (ir_code_ack && ir_code == databuf));

  // Code stability between acks and before release
  assert property ($past(reset_n) &&
                   $past(!(bits_detected == 32 && (databuf[15:8] == ~databuf[7:0]))) &&
                   $past(rpt_cnt < RPT_RELEASE_THOLD)
                   |-> ir_code == $past(ir_code));

  // Release clears outputs
  assert property (rpt_cnt >= RPT_RELEASE_THOLD |-> (ir_code == 32'h0 && ir_code_ack == 1'b0));

  // Coverage
  cover property ($rose(ir_code_ack));
  cover property (state == STATE_LEADVERIFY && leadvrf_cnt == LEADCODE_HI_RPT_THOLD ##1 rpt_cnt == 0);
  cover property (state == STATE_DATARCV && datarcv_cnt == BIT_ONE_THOLD);
  cover property (state == STATE_DATARCV && (datarcv_cnt >= IDLE_THOLD || bits_detected >= 33) ##1 state == STATE_IDLE);

endmodule
`endif