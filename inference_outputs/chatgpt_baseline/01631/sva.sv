module sky130_fd_sc_hd__o2bb2a_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    // X implements (~(A1_N & A2_N)) & (B1 | B2).
    check_function_equation: assert property (
        @(posedge $global_clock) X == ((~(A1_N & A2_N)) & (B1 | B2))
    );

    // If both B inputs are 0, X must be 0.
    check_low_when_Bs_zero: assert property (
        @(posedge $global_clock) ((B1 | B2) == 1'b0) |-> (X == 1'b0)
    );

    // If both A_N inputs are 1, X must be 0.
    check_low_when_As_both_one: assert property (
        @(posedge $global_clock) ((A1_N & A2_N) == 1'b1) |-> (X == 1'b0)
    );

    // If both factors are 1, X must be 1.
    check_high_when_factors_one: assert property (
        @(posedge $global_clock) (((~(A1_N & A2_N)) == 1'b1) && ((B1 | B2) == 1'b1)) |-> (X == 1'b1)
    );

    // X=1 implies B1|B2 is 1.
    check_X1_implies_B_or1: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> ((B1 | B2) == 1'b1)
    );

    // X=1 implies ~(A1_N & A2_N) is 1.
    check_X1_implies_A_factor1: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> ((~(A1_N & A2_N)) == 1'b1)
    );

    // X=0 implies at least one factor is 0.
    check_X0_implies_factor0: assert property (
        @(posedge $global_clock) (X == 1'b0) |-> (((B1 | B2) == 1'b0) || ((A1_N & A2_N) == 1'b1))
    );

    // When ~(A1_N & A2_N)=1, X equals B1|B2.
    check_A_factor1_equals_B_or: assert property (
        @(posedge $global_clock) ((~(A1_N & A2_N)) == 1'b1) |-> (X == (B1 | B2))
    );

    // When B1|B2=1, X equals ~(A1_N & A2_N).
    check_B_or1_equals_nandA: assert property (
        @(posedge $global_clock) ((B1 | B2) == 1'b1) |-> (X == (~(A1_N & A2_N)))
    );

    // If both factors are 0, X must be 0.
    check_both_factors_zero_implies_X0: assert property (
        @(posedge $global_clock) (((~(A1_N & A2_N)) == 1'b0) && ((B1 | B2) == 1'b0)) |-> (X == 1'b0)
    );
endmodule