module my_module_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Clocking on any input edge (no explicit clock/reset in RTL)
`define SVA_CLK (posedge A1_N or negedge A1_N or \
                 posedge A2_N or negedge A2_N or \
                 posedge B1   or negedge B1   or \
                 posedge B2   or negedge B2   or \
                 posedge VPWR or negedge VPWR or \
                 posedge VGND or negedge VGND or \
                 posedge VPB  or negedge VPB  or \
                 posedge VNB  or negedge VNB)

    // Y matches the exact RTL boolean expression.
    check_function_equivalence_exact: assert property (
        @`SVA_CLK Y == (((A1_N & ~A2_N) & B1) | ((~A1_N & A2_N) & B2) | ((~A1_N & ~A2_N) & 1'b0) | ((A1_N & A2_N) & 1'b1))
    );

    // When both selects are 1, Y must be 1.
    check_case_both_one: assert property (
        @`SVA_CLK (A1_N & A2_N) |=> (Y == 1'b1)
    );

    // When both selects are 0, Y must be 0.
    check_case_both_zero: assert property (
        @`SVA_CLK (~A1_N & ~A2_N) |=> (Y == 1'b0)
    );

    // When A1_N=1 and A2_N=0, Y equals B1.
    check_case_select_b1: assert property (
        @`SVA_CLK (A1_N & ~A2_N) |=> (Y == B1)
    );

    // When A1_N=0 and A2_N=1, Y equals B2.
    check_case_select_b2: assert property (
        @`SVA_CLK (~A1_N & A2_N) |=> (Y == B2)
    );

    // Selected B1 high drives Y high.
    check_b1_selected_high: assert property (
        @`SVA_CLK (A1_N & ~A2_N & B1) |=> (Y == 1'b1)
    );

    // Selected B1 low drives Y low.
    check_b1_selected_low: assert property (
        @`SVA_CLK (A1_N & ~A2_N & ~B1) |=> (Y == 1'b0)
    );

    // Selected B2 high drives Y high.
    check_b2_selected_high: assert property (
        @`SVA_CLK (~A1_N & A2_N & B2) |=> (Y == 1'b1)
    );

    // Selected B2 low drives Y low.
    check_b2_selected_low: assert property (
        @`SVA_CLK (~A1_N & A2_N & ~B2) |=> (Y == 1'b0)
    );

    // When exactly one select is 1, Y behaves as a mux of B1/B2.
    check_xor_select_mux: assert property (
        @`SVA_CLK (A1_N ^ A2_N) |=> (Y == (A1_N ? B1 : B2))
    );

endmodule