module mux_dff_sva (
    input logic Q,
    input logic Q_N,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE
);

    // Q_N is always the inverse of Q.
    check_qn_complement: assert property (
        @(posedge CLK) (Q_N == ~Q)
    );

    // With both select controls low, the mux drives 0.
    check_mux_zero_when_selects_low: assert property (
        @(posedge CLK) (!SCD && !SCE) |-> ((Q == 1'b0) && (Q_N == 1'b1))
    );

    // With SCD high and SCE low, the mux drives D.
    check_mux_selects_d_when_scd_high_sce_low: assert property (
        @(posedge CLK) (SCD && !SCE) |-> ((Q == D) && (Q_N == ~D))
    );

    // With SCE high and SCD low, the mux drives 0.
    check_mux_zero_when_sce_high_scd_low: assert property (
        @(posedge CLK) (!SCD && SCE) |-> ((Q == 1'b0) && (Q_N == 1'b1))
    );

    // With both select controls high, the mux drives 0.
    check_mux_zero_when_selects_high: assert property (
        @(posedge CLK) (SCD && SCE) |-> ((Q == 1'b0) && (Q_N == 1'b1))
    );

    // With both select controls low, the next-cycle Q reflects D.
    check_next_cycle_q_reflects_d_when_selects_low: assert property (
        @(posedge CLK) (!SCD && !SCE) |=> (Q == $past(D))
    );

    // With SCD high and SCE low, the next-cycle Q reflects D.
    check_next_cycle_q_reflects_d_when_scd_high_sce_low: assert property (
        @(posedge CLK) (SCD && !SCE) |=> (Q == $past(D))
    );

    // With SCE high and SCD low, the next-cycle Q is 0.
    check_next_cycle_q_zero_when_sce_high_scd_low: assert property (
        @(posedge CLK) (!SCD && SCE) |=> (Q == 1'b0)
    );

    // With both select controls high, the next-cycle Q is 0.
    check_next_cycle_q_zero_when_selects_high: assert property (
        @(posedge CLK) (SCD && SCE) |=> (Q == 1'b0)
    );

endmodule