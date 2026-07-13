module Reset_Delay_sva (
    input logic iCLK,
    input logic iRST,
    input logic oRST_0,
    input logic oRST_1,
    input logic oRST_2
);

    // Formal starts with reset asserted.
    init_reset_assumption: assume property (
        @(posedge iCLK) $initstate |-> (iRST == 1'b0)
    );

    // Active-low reset clears all delayed reset outputs.
    check_reset_clears_outputs: assert property (
        @(posedge iCLK) (!iRST) |-> ((oRST_0 == 1'b0) && (oRST_1 == 1'b0) && (oRST_2 == 1'b0))
    );

    // The first sampled cycle after reset release still has all outputs low.
    check_release_keeps_outputs_low: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $rose(iRST) |-> ((oRST_0 == 1'b0) && (oRST_1 == 1'b0) && (oRST_2 == 1'b0))
    );

    // oRST_0 stays high until reset once it has asserted.
    check_oRST_0_sticky_high: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $past(oRST_0) |-> (oRST_0 == 1'b1)
    );

    // oRST_1 stays high until reset once it has asserted.
    check_oRST_1_sticky_high: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $past(oRST_1) |-> (oRST_1 == 1'b1)
    );

    // oRST_2 stays high until reset once it has asserted.
    check_oRST_2_sticky_high: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $past(oRST_2) |-> (oRST_2 == 1'b1)
    );

    // oRST_1 cannot be high unless oRST_0 is already high.
    check_oRST_1_requires_oRST_0: assert property (
        @(posedge iCLK) disable iff (!iRST)
        (oRST_1 == 1'b1) |-> (oRST_0 == 1'b1)
    );

    // oRST_2 cannot be high unless both earlier outputs are high.
    check_oRST_2_requires_lower_resets: assert property (
        @(posedge iCLK) disable iff (!iRST)
        (oRST_2 == 1'b1) |-> ((oRST_1 == 1'b1) && (oRST_0 == 1'b1))
    );

    // oRST_0 asserts before either later delayed reset asserts.
    check_oRST_0_rises_first: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $rose(oRST_0) |-> ((oRST_1 == 1'b0) && (oRST_2 == 1'b0))
    );

    // oRST_1 asserts only after oRST_0 and before oRST_2.
    check_oRST_1_rises_second: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $rose(oRST_1) |-> ((oRST_0 == 1'b1) && (oRST_2 == 1'b0))
    );

    // oRST_2 asserts only after both earlier delayed resets are high.
    check_oRST_2_rises_last: assert property (
        @(posedge iCLK) disable iff (!iRST)
        $rose(oRST_2) |-> ((oRST_0 == 1'b1) && (oRST_1 == 1'b1))
    );

endmodule