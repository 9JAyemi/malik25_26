module sky130_fd_sc_hs__a2bb2o_sva (
    input logic CLK,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic X
);
    // Functional equivalence to boolean definition.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((B2 || A2_N) && (B1 || A1_N))
    );

    // If both OR terms are true, X must be 1.
    check_one_when_both_or_terms_true: assert property (
        @(posedge CLK) ((B2 || A2_N) && (B1 || A1_N)) |-> (X == 1'b1)
    );

    // X high implies (B2 || A2_N) is true.
    check_x_high_implies_or2_true: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B2 || A2_N)
    );

    // X high implies (B1 || A1_N) is true.
    check_x_high_implies_or1_true: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B1 || A1_N)
    );

    // If B2 and A2_N are both 0, X must be 0.
    check_zero_when_B2_and_A2N_zero: assert property (
        @(posedge CLK) (!B2 && !A2_N) |-> (X == 1'b0)
    );

    // If B1 and A1_N are both 0, X must be 0.
    check_zero_when_B1_and_A1N_zero: assert property (
        @(posedge CLK) (!B1 && !A1_N) |-> (X == 1'b0)
    );

    // When A1_N and A2_N are 0, X reduces to B1 & B2.
    check_reduction_when_As_low: assert property (
        @(posedge CLK) (!A1_N && !A2_N) |-> (X == (B1 && B2))
    );

    // When B1 and B2 are 0, X reduces to A1_N & A2_N.
    check_reduction_when_Bs_low: assert property (
        @(posedge CLK) (!B1 && !B2) |-> (X == (A1_N && A2_N))
    );

    // When B1 and B2 are 1, X must be 1.
    check_one_when_Bs_one: assert property (
        @(posedge CLK) (B1 && B2) |-> (X == 1'b1)
    );

    // When A1_N and A2_N are 1, X must be 1.
    check_one_when_As_one: assert property (
        @(posedge CLK) (A1_N && A2_N) |-> (X == 1'b1)
    );
endmodule