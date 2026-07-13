module arithmetic_operation_sva (
    input logic clk,
    input logic ADDSUB,
    input logic [26:0] D_DATA,
    input logic INMODE2,
    input logic [26:0] PREADD_AB,
    input logic [26:0] AD
);

    // AD must match the combinational add/sub result selected by ADDSUB and INMODE2.
    check_ad_matches_rtl_equation: assert property (
        @(posedge clk)
        AD == (ADDSUB ? ((INMODE2 ? D_DATA : 27'b0) - PREADD_AB)
                      : ((INMODE2 ? D_DATA : 27'b0) + PREADD_AB))
    );

    // With INMODE2 low and add selected, AD equals PREADD_AB.
    check_add_with_inmode2_low: assert property (
        @(posedge clk)
        (!INMODE2 && !ADDSUB) |-> (AD == PREADD_AB)
    );

    // With INMODE2 low and subtract selected, AD equals 0 minus PREADD_AB.
    check_sub_with_inmode2_low: assert property (
        @(posedge clk)
        (!INMODE2 && ADDSUB) |-> (AD == (27'b0 - PREADD_AB))
    );

    // With INMODE2 high and add selected, AD equals D_DATA plus PREADD_AB.
    check_add_with_inmode2_high: assert property (
        @(posedge clk)
        (INMODE2 && !ADDSUB) |-> (AD == (D_DATA + PREADD_AB))
    );

    // With INMODE2 high and subtract selected, AD equals D_DATA minus PREADD_AB.
    check_sub_with_inmode2_high: assert property (
        @(posedge clk)
        (INMODE2 && ADDSUB) |-> (AD == (D_DATA - PREADD_AB))
    );

endmodule