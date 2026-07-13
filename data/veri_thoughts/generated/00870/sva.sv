module and_nand_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic nand0_out,
    input logic nand1_out
);
    // Y is the AND of the two NAND outputs.
    check_y_is_and_of_nands: assert property (
        @(posedge CLK) Y == (nand0_out & nand1_out)
    );

    // nand0_out implements ~(A1 & A2 & A3).
    check_nand0_function: assert property (
        @(posedge CLK) nand0_out == ~(A1 & A2 & A3)
    );

    // nand1_out implements ~(B1 & B2).
    check_nand1_function: assert property (
        @(posedge CLK) nand1_out == ~(B1 & B2)
    );

    // nand0_out is LOW when all A inputs are HIGH.
    check_nand0_low_when_all_ones: assert property (
        @(posedge CLK) (A1 & A2 & A3) |-> (nand0_out == 1'b0)
    );

    // nand0_out is HIGH when any A input is LOW.
    check_nand0_high_when_any_zero: assert property (
        @(posedge CLK) ((!A1) || (!A2) || (!A3)) |-> (nand0_out == 1'b1)
    );

    // nand1_out is LOW when both B inputs are HIGH.
    check_nand1_low_when_all_ones: assert property (
        @(posedge CLK) (B1 & B2) |-> (nand1_out == 1'b0)
    );

    // nand1_out is HIGH when any B input is LOW.
    check_nand1_high_when_any_zero: assert property (
        @(posedge CLK) ((!B1) || (!B2)) |-> (nand1_out == 1'b1)
    );

    // Y is LOW when all A inputs are HIGH.
    check_y_low_when_a_all_ones: assert property (
        @(posedge CLK) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // Y is LOW when both B inputs are HIGH.
    check_y_low_when_b_all_ones: assert property (
        @(posedge CLK) (B1 & B2) |-> (Y == 1'b0)
    );

    // Y is HIGH when at least one A is LOW and at least one B is LOW.
    check_y_high_when_both_groups_have_zero: assert property (
        @(posedge CLK) (((!A1) || (!A2) || (!A3)) && ((!B1) || (!B2))) |-> (Y == 1'b1)
    );

    // Y matches the combined boolean function ~(A1&A2&A3) & ~(B1&B2).
    check_y_matches_boolean_function: assert property (
        @(posedge CLK) Y == ((~(A1 & A2 & A3)) & (~(B1 & B2)))
    );
endmodule