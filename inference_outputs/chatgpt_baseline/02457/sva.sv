module digital_circuit_sva (
    input logic D,
    input logic Q,
    input logic Q_N,
    input logic SCD,
    input logic SCE,
    input logic CLK,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    ///// Output relationships /////
    // Q_N is always the bitwise inverse of Q.
    check_qn_is_invert_of_q: assert property (
        @(posedge CLK) (Q_N === ~Q)
    );

    ///// Capture behavior /////
    // Q captures the selected input (SCE ? SCD : D) from the previous cycle.
    check_q_captures_mux_prev: assert property (
        @(posedge CLK) 1'b1 ##1 (Q == $past(SCE ? SCD : D))
    );

    // Q_N captures the inverse of the selected input from the previous cycle.
    check_qn_captures_inverted_mux_prev: assert property (
        @(posedge CLK) 1'b1 ##1 (Q_N === ~$past(SCE ? SCD : D))
    );

    ///// Scan enable selection /////
    // When SCE=0, Q captures D on the next rising edge.
    check_q_from_d_when_sce0: assert property (
        @(posedge CLK) (SCE == 1'b0) |=> (Q == $past(D))
    );

    // When SCE=1, Q captures SCD on the next rising edge.
    check_q_from_scd_when_sce1: assert property (
        @(posedge CLK) (SCE == 1'b1) |=> (Q == $past(SCD))
    );

    // When SCE=0, Q_N captures ~D on the next rising edge.
    check_qn_from_d_when_sce0: assert property (
        @(posedge CLK) (SCE == 1'b0) |=> (Q_N === ~$past(D))
    );

    // When SCE=1, Q_N captures ~SCD on the next rising edge.
    check_qn_from_scd_when_sce1: assert property (
        @(posedge CLK) (SCE == 1'b1) |=> (Q_N === ~$past(SCD))
    );

endmodule