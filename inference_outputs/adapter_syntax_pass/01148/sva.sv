module and3b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must match the RTL's conditional expression.
    check_x_matches_rtl_expression: assert property (
        @($global_clock)
        X == ((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1)) ? 1'b1 :
             ((A_N == 1'b0) || (B == 1'b0) || (C == 1'b0)) ? 1'b0 :
             1'bx
    );

    // X must be high when all three inputs are high.
    check_x_high_when_all_inputs_high: assert property (
        @($global_clock)
        ((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // X must be low when any input is low.
    check_x_low_when_any_input_low: assert property (
        @($global_clock)
        ((A_N == 1'b0) || (B == 1'b0) || (C == 1'b0)) |-> (X == 1'b0)
    );

    // X must be high-impedance when the first branch is not taken.
    check_x_highz_when_first_branch_not_taken: assert property (
        @($global_clock)
        !((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (X == 1'bx)
    );

    // X must be high-impedance when the second branch is not taken.
    check_x_highz_when_second_branch_not_taken: assert property (
        @($global_clock)
        !((A_N == 1'b0) || (B == 1'b0) || (C == 1'b0)) |-> (X == 1'bx)
    );

endmodule