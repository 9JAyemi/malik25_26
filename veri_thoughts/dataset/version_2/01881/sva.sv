module sky130_fd_sc_hdll__a32o_sva (
    input  logic CLK,
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic A3,
    input  logic B1,
    input  logic B2
);
    ///// Boolean function rules /////
    // X equals (A1&A2&A3) OR (B1&B2).
    check_x_functional_equivalence: assert property (
        @(posedge CLK) X == ((A1 && A2 && A3) || (B1 && B2))
    );

    // If A1&A2&A3 are all 1, X must be 1.
    check_x_high_when_all_A: assert property (
        @(posedge CLK) (A1 && A2 && A3) |-> (X == 1'b1)
    );

    // If B1&B2 are 1, X must be 1.
    check_x_high_when_all_B: assert property (
        @(posedge CLK) (B1 && B2) |-> (X == 1'b1)
    );

    // If X is 1, at least one product term is 1.
    check_x_high_implies_term: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A1 && A2 && A3) || (B1 && B2))
    );

    // If neither product term is 1, X must be 0.
    check_x_low_implies_no_term: assert property (
        @(posedge CLK) (!(A1 && A2 && A3) && !(B1 && B2)) |-> (X == 1'b0)
    );

    ///// Conditional transparency rules /////
    // With A1&A2=1 and B-term=0, X equals A3.
    check_x_equals_A3_when_A1A2_and_notB: assert property (
        @(posedge CLK) (A1 && A2 && !(B1 && B2)) |-> (X == A3)
    );

    // With A1&A3=1 and B-term=0, X equals A2.
    check_x_equals_A2_when_A1A3_and_notB: assert property (
        @(posedge CLK) (A1 && A3 && !(B1 && B2)) |-> (X == A2)
    );

    // With A2&A3=1 and B-term=0, X equals A1.
    check_x_equals_A1_when_A2A3_and_notB: assert property (
        @(posedge CLK) (A2 && A3 && !(B1 && B2)) |-> (X == A1)
    );

    // With B1=1 and A-term=0, X equals B2.
    check_x_equals_B2_when_B1_and_notA: assert property (
        @(posedge CLK) (B1 && !(A1 && A2 && A3)) |-> (X == B2)
    );

    // With B2=1 and A-term=0, X equals B1.
    check_x_equals_B1_when_B2_and_notA: assert property (
        @(posedge CLK) (B2 && !(A1 && A2 && A3)) |-> (X == B1)
    );
endmodule