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

    // When SCE is high, Q captures SCD on the next clock.
    check_capture_scd_when_sce_high: assert property (
        @(posedge CLK) SCE |=> (Q == $past(SCD))
    );

    // When SCE is low, Q captures D on the next clock.
    check_capture_d_when_sce_low: assert property (
        @(posedge CLK) !SCE |=> (Q == $past(D))
    );

    // Q_N reflects the inverse of the captured input on the next clock.
    check_qn_matches_captured_input: assert property (
        @(posedge CLK) 1'b1 |=> (Q_N == ~($past(SCE) ? $past(SCD) : $past(D)))
    );

endmodule