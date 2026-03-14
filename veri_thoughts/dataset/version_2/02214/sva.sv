module ir_rcv_sva (
    input logic        clk50,
    input logic        reset_n,
    input logic        ir_rx,
    input logic [31:0] ir_code,
    input logic        ir_code_ack,
    input logic [1:0]  state,
    input logic [31:0] databuf,
    input logic [5:0]  bits_detected,
    input logic [17:0] act_cnt,
    input logic [17:0] leadvrf_cnt,
    input logic [17:0] datarcv_cnt,
    input logic [22:0] rpt_cnt
);
    // Clk/Reset: clk50 posedge; reset_n active-low async
    // Logic style: sequential (all regs in posedge FFs)
    // Key behaviors: counters conditioned by state/ir_rx, 3-state FSM, ir_code/ack update on decode, release timeout reset

    // State encodings
    localparam logic [1:0] STATE_IDLE       = 2'b00;
    localparam logic [1:0] STATE_LEADVERIFY = 2'b01;
    localparam logic [1:0] STATE_DATARCV    = 2'b10;

    // Thresholds (match RTL)
    parameter int unsigned LEADCODE_LO_THOLD      = 230000;
    parameter int unsigned LEADCODE_HI_THOLD      = 210000;
    parameter int unsigned LEADCODE_HI_RPT_THOLD  = 105000;
    parameter int unsigned RPT_RELEASE_THOLD      = 6000000;
    parameter int unsigned BIT_ONE_THOLD          = 41500;
    parameter int unsigned BIT_DETECT_THOLD       = 20000;
    parameter int unsigned IDLE_THOLD             = 262143;

    ///// Reset behavior /////
    // On reset assertion, all regs/counters/outputs are cleared and state is IDLE.
    check_reset_values: assert property (
        @(posedge clk50) !reset_n |-> (state == STATE_IDLE)
                                   && (act_cnt == 18'd0)
                                   && (leadvrf_cnt == 18'd0)
                                   && (datarcv_cnt == 18'd0)
                                   && (bits_detected == 6'd0)
                                   && (databuf == 32'h0000_0000)
                                   && (rpt_cnt == 23'd0)
                                   && (ir_code == 32'h0000_0000)
                                   && (ir_code_ack == 1'b0)
    );

    ///// act_cnt rules /////
    // When in IDLE and ir_rx LOW, act_cnt increments by 1.
    check_act_cnt_incr: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_IDLE && $past(ir_rx) == 1'b0)
            |-> (act_cnt == $past(act_cnt) + 1)
    );
    // Otherwise, act_cnt clears to 0.
    check_act_cnt_clear: assert property (
        @(posedge clk50) disable iff (!reset_n)
            !($past(state) == STATE_IDLE && $past(ir_rx) == 1'b0)
            |-> (act_cnt == 18'd0)
    );

    ///// leadvrf_cnt rules /////
    // When in LEADVERIFY and ir_rx HIGH, leadvrf_cnt increments by 1.
    check_leadvrf_incr: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_LEADVERIFY && $past(ir_rx) == 1'b1)
            |-> (leadvrf_cnt == $past(leadvrf_cnt) + 1)
    );
    // Otherwise, leadvrf_cnt clears to 0.
    check_leadvrf_clear: assert property (
        @(posedge clk50) disable iff (!reset_n)
            !($past(state) == STATE_LEADVERIFY && $past(ir_rx) == 1'b1)
            |-> (leadvrf_cnt == 18'd0)
    );

    ///// datarcv_cnt rules /////
    // When in DATARCV and ir_rx HIGH, datarcv_cnt increments by 1.
    check_datarcv_incr: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && $past(ir_rx) == 1'b1)
            |-> (datarcv_cnt == $past(datarcv_cnt) + 1)
    );
    // Otherwise, datarcv_cnt clears to 0.
    check_datarcv_clear: assert property (
        @(posedge clk50) disable iff (!reset_n)
            !($past(state) == STATE_DATARCV && $past(ir_rx) == 1'b1)
            |-> (datarcv_cnt == 18'd0)
    );

    ///// bits_detected rules /////
    // Outside DATARCV, bits_detected clears to 0.
    check_bits_clear_outside_datarcv: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) != STATE_DATARCV) |-> (bits_detected == 6'd0)
    );
    // In DATARCV, on BIT_DETECT_THOLD, bits_detected increments by 1.
    check_bits_incr_on_detect: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && $past(datarcv_cnt) == BIT_DETECT_THOLD)
            |-> (bits_detected == $past(bits_detected) + 1)
    );
    // In DATARCV without detect, bits_detected holds its value.
    check_bits_hold_no_detect: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && $past(datarcv_cnt) != BIT_DETECT_THOLD)
            |-> (bits_detected == $past(bits_detected))
    );

    ///// databuf rules /////
    // Outside DATARCV, databuf clears to 0.
    check_databuf_clear_outside_datarcv: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) != STATE_DATARCV) |-> (databuf == 32'h0000_0000)
    );
    // In DATARCV without BIT_ONE_THOLD, databuf holds its value.
    check_databuf_hold_no_one_thold: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && $past(datarcv_cnt) != BIT_ONE_THOLD)
            |-> (databuf == $past(databuf))
    );
    // On BIT_ONE_THOLD in DATARCV, the indexed bit is set to 1.
    check_databuf_set_on_one_thold: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && $past(datarcv_cnt) == BIT_ONE_THOLD && $past(bits_detected) <= 6'd32)
            |-> (databuf[32 - $past(bits_detected)] == 1'b1)
    );

    ///// ir_code_ack and ir_code rules /////
    // ir_code_ack equals the decode condition (bits==32 and byte complement).
    check_ack_equals_decode: assert property (
        @(posedge clk50) disable iff (!reset_n)
            (ir_code_ack == ( ($past(bits_detected) == 6'd32) && ($past(databuf[15:8]) == ~ $past(databuf[7:0])) ))
    );
    // When ack is asserted, ir_code updates to prior databuf.
    check_code_updates_on_ack: assert property (
        @(posedge clk50) disable iff (!reset_n)
            (ir_code_ack) |-> (ir_code == $past(databuf))
    );
    // On release timeout (when decode is not true), code and ack clear.
    check_release_clears_code_ack: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(rpt_cnt) >= RPT_RELEASE_THOLD
             && !(($past(bits_detected) == 6'd32) && ($past(databuf[15:8]) == ~ $past(databuf[7:0]))))
            |-> (ir_code == 32'h0000_0000 && ir_code_ack == 1'b0)
    );
    // When neither decode nor release occurs, ir_code holds its value.
    check_code_holds_no_event: assert property (
        @(posedge clk50) disable iff (!reset_n)
            (! (($past(bits_detected) == 6'd32) && ($past(databuf[15:8]) == ~ $past(databuf[7:0])))
             && !($past(rpt_cnt) >= RPT_RELEASE_THOLD))
            |-> (ir_code == $past(ir_code))
    );

    ///// rpt_cnt rules /////
    // rpt_cnt resets to 0 on LEADVERIFY HI repeat threshold.
    check_rpt_cnt_reset_on_lead_rpt: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_LEADVERIFY && $past(leadvrf_cnt) == LEADCODE_HI_RPT_THOLD)
            |-> (rpt_cnt == 23'd0)
    );
    // Otherwise, rpt_cnt increments by 1.
    check_rpt_cnt_incr_otherwise: assert property (
        @(posedge clk50) disable iff (!reset_n)
            !($past(state) == STATE_LEADVERIFY && $past(leadvrf_cnt) == LEADCODE_HI_RPT_THOLD)
            |-> (rpt_cnt == $past(rpt_cnt) + 1)
    );

    ///// FSM transition rules /////
    // IDLE -> LEADVERIFY when act_cnt crosses low threshold.
    check_idle_to_leadverify: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_IDLE && $past(act_cnt) >= LEADCODE_LO_THOLD)
            |-> (state == STATE_LEADVERIFY)
    );
    // LEADVERIFY -> DATARCV when leadvrf_cnt crosses high threshold.
    check_leadverify_to_datarcv: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_LEADVERIFY && $past(leadvrf_cnt) >= LEADCODE_HI_THOLD)
            |-> (state == STATE_DATARCV)
    );
    // DATARCV -> IDLE on long idle or too many bits.
    check_datarcv_to_idle: assert property (
        @(posedge clk50) disable iff (!reset_n)
            ($past(state) == STATE_DATARCV && ($past(datarcv_cnt) >= IDLE_THOLD || $past(bits_detected) >= 6'd33))
            |-> (state == STATE_IDLE)
    );

endmodule