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

    // Q_N is always the inverse of Q.
    check_qn_complement: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    // When SCE is high, the next-cycle output reflects SCD.
    check_select_scd: assert property (
        @(posedge CLK) SCE |=> (Q == $past(SCD)) && (Q_N == ~$past(SCD))
    );

    // When SCE is low, the next-cycle output reflects D.
    check_select_d: assert property (
        @(posedge CLK) !SCE |=> (Q == $past(D)) && (Q_N == ~$past(D))
    );

    // A sampled high Q must come from the previously selected input.
    check_q_high_source: assert property (
        @(posedge CLK) Q |=> (($past(SCE) ? $past(SCD) : $past(D)) == 1'b1)
    );

    // A sampled low Q must come from the previously selected input.
    check_q_low_source: assert property (
        @(posedge CLK) !Q |=> (($past(SCE) ? $past(SCD) : $past(D)) == 1'b0)
    );

    // A sampled high Q_N must come from the previously selected input.
    check_qn_high_source: assert property (
        @(posedge CLK) Q_N |=> (($past(SCE) ? $past(SCD) : $past(D)) == 1'b0)
    );

    // A sampled low Q_N must come from the previously selected input.
    check_qn_low_source: assert property (
        @(posedge CLK) !Q_N |=> (($past(SCE) ? $past(SCD) : $past(D)) == 1'b1)
    );

endmodule