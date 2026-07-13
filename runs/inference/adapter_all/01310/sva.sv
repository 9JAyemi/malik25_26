module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK equals previous cycle's (EN & TE) OR (~EN & 0).
    check_enclk_update_function: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK == $past(EN & TE)
    );

    // When EN is 1, ENCLK captures TE from the previous cycle.
    check_capture_when_en: assert property (
        @(posedge CLK) disable iff ($initstate) EN |-> (ENCLK == $past(TE))
    );

    // When EN is 0, ENCLK clears to 0 on the next cycle.
    check_clear_when_en0: assert property (
        @(posedge CLK) disable iff ($initstate) !EN |-> ##1 (ENCLK == 1'b0)
    );

    // If EN and TE were both 1 in the previous cycle, ENCLK is 1 now.
    check_prev_en_and_te_sets: assert property (
        @(posedge CLK) disable iff ($initstate) $past(EN && TE) |-> (ENCLK == 1'b1)
    );

    // If EN was 0 in the previous cycle, ENCLK is 0 now.
    check_prev_en0_clears: assert property (
        @(posedge CLK) disable iff ($initstate) $past(!EN) |-> (ENCLK == 1'b0)
    );

    // If TE was 0 in the previous cycle and EN was 1, ENCLK is 0 now.
    check_prev_te0_with_en_clears: assert property (
        @(posedge CLK) disable iff ($initstate) $past(EN && !TE) |-> (ENCLK == 1'b0)
    );

    // If ENCLK is 1 now, the previous cycle had EN and TE both 1.
    check_enclk1_implies_prev_en_and_te: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK |-> $past(EN && TE)
    );

    // If ENCLK is 0 now, the previous cycle had either EN=0 or TE=0.
    check_enclk0_implies_prev_en0_or_te0: assert property (
        @(posedge CLK) disable iff ($initstate) !ENCLK |-> $past(!EN || !TE)
    );

    // If EN and TE were both 1 in the previous cycle, ENCLK is 1 now.
    check_prev_en_and_te_sets: assert property (
        @(posedge CLK) disable iff ($initstate) $past(EN && TE) |-> (ENCLK == 1'b1)
    );

    // If EN was 0 in the previous cycle, ENCLK is 0 now.
    check_prev_en0_clears: assert property (
        @(posedge CLK) disable iff ($initstate) $past(!EN) |-> (ENCLK == 1'b0)
    );
endmodule