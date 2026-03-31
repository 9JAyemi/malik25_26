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
        @(posedge CLK) Q_N == ~Q
    );

    // With both select controls low, the output is low.
    check_default_low: assert property (
        @(posedge CLK) (!SCD && !SCE) |-> (Q == 1'b0)
    );

    // With SCD high and SCE low, the output follows D.
    check_select_d_when_scd_only: assert property (
        @(posedge CLK) (SCD && !SCE) |-> (Q == D)
    );

    // With SCE high and SCD low, the output is low.
    check_select_low_when_sce_only: assert property (
        @(posedge CLK) (!SCD && SCE) |-> (Q == 1'b0)
    );

    // With both select controls high, the output is high.
    check_select_high_when_both_high: assert property (
        @(posedge CLK) (SCD && SCE) |-> (Q == 1'b1)
    );

    // With SCD high and SCE high, the output is high.
    check_scd_and_sce_high_sets_q: assert property (
        @(posedge CLK) (SCD && SCE) |-> (Q == 1'b1)
    );

    // With SCD high and SCE low, a high D is captured into Q.
    check_capture_d_when_scd_only: assert property (
        @(posedge CLK) (SCD && !SCE && D) |=> (Q == 1'b1)
    );

    // With SCD high and SCE low, a low D is captured into Q.
    check_capture_low_when_scd_only: assert property (
        @(posedge CLK) (SCD && !SCE && !D) |=> (Q == 1'b0)
    );

endmodule