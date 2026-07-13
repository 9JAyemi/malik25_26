module lead0_count_sva (
    input logic CLK,
    input logic RESETn,

    input logic din_15_8_eq_0,
    input logic din_15_12_eq_0,
    input logic lead0_8b_1_hi,
    input logic lead0_8b_0_hi,
    input logic din_7_0_eq_0,
    input logic din_7_4_eq_0,
    input logic lead0_8b_1_lo,
    input logic lead0_8b_0_lo,
    input logic din_15_0_eq_0,
    input logic lead0_16b_2,
    input logic lead0_16b_1,
    input logic lead0_16b_0
);

    ///// Functional definitions /////
    // din_15_0_eq_0 equals din_15_8_eq_0 AND din_7_0_eq_0.
    check_def_din_15_0_eq_0: assert property (
        @(posedge CLK) disable iff (!RESETn) din_15_0_eq_0 == (din_15_8_eq_0 && din_7_0_eq_0)
    );

    // lead0_16b_2 equals ((!din_15_8_eq_0)&&din_15_12_eq_0) || (din_15_8_eq_0&&din_7_4_eq_0).
    check_def_lead0_16b_2: assert property (
        @(posedge CLK) disable iff (!RESETn) lead0_16b_2 == (((!din_15_8_eq_0) && din_15_12_eq_0) || (din_15_8_eq_0 && din_7_4_eq_0))
    );

    // lead0_16b_1 equals ((!din_15_8_eq_0)&&lead0_8b_1_hi) || (din_15_8_eq_0&&lead0_8b_1_lo).
    check_def_lead0_16b_1: assert property (
        @(posedge CLK) disable iff (!RESETn) lead0_16b_1 == (((!din_15_8_eq_0) && lead0_8b_1_hi) || (din_15_8_eq_0 && lead0_8b_1_lo))
    );

    // lead0_16b_0 equals ((!din_15_8_eq_0)&&lead0_8b_0_hi) || (din_15_8_eq_0&&lead0_8b_0_lo).
    check_def_lead0_16b_0: assert property (
        @(posedge CLK) disable iff (!RESETn) lead0_16b_0 == (((!din_15_8_eq_0) && lead0_8b_0_hi) || (din_15_8_eq_0 && lead0_8b_0_lo))
    );

    ///// MUX select behavior /////
    // When din_15_8_eq_0==0, lead0_16b_2 follows din_15_12_eq_0.
    check_mux_lead0_16b_2_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (!din_15_8_eq_0) |-> (lead0_16b_2 == din_15_12_eq_0)
    );

    // When din_15_8_eq_0==1, lead0_16b_2 follows din_7_4_eq_0.
    check_mux_lead0_16b_2_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (din_15_8_eq_0) |-> (lead0_16b_2 == din_7_4_eq_0)
    );

    // When din_15_8_eq_0==0, lead0_16b_1 follows lead0_8b_1_hi.
    check_mux_lead0_16b_1_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (!din_15_8_eq_0) |-> (lead0_16b_1 == lead0_8b_1_hi)
    );

    // When din_15_8_eq_0==1, lead0_16b_1 follows lead0_8b_1_lo.
    check_mux_lead0_16b_1_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (din_15_8_eq_0) |-> (lead0_16b_1 == lead0_8b_1_lo)
    );

    // When din_15_8_eq_0==0, lead0_16b_0 follows lead0_8b_0_hi.
    check_mux_lead0_16b_0_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (!din_15_8_eq_0) |-> (lead0_16b_0 == lead0_8b_0_hi)
    );

    // When din_15_8_eq_0==1, lead0_16b_0 follows lead0_8b_0_lo.
    check_mux_lead0_16b_0_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (din_15_8_eq_0) |-> (lead0_16b_0 == lead0_8b_0_lo)
    );

endmodule