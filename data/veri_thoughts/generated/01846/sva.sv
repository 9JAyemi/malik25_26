module logic_circuit_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);
    // X implements (A1 & A2) | B1.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((A1 & A2) | B1)
    );

    // B1=1 forces X=1.
    check_B1_dominates_output_high: assert property (
        @(posedge CLK) B1 |=> (X == 1'b1)
    );

    // A1=1 and A2=1 force X=1.
    check_and_both_high_sets_output: assert property (
        @(posedge CLK) (A1 && A2) |=> (X == 1'b1)
    );

    // X=0 implies B1=0 and not(A1&A2).
    check_output_zero_implies_inputs: assert property (
        @(posedge CLK) (X == 1'b0) |=> ((B1 == 1'b0) && !(A1 && A2))
    );

    // X=1 implies B1=1 or (A1&A2)=1.
    check_output_one_has_cause: assert property (
        @(posedge CLK) (X == 1'b1) |=> ((B1 == 1'b1) || (A1 && A2))
    );

    // When B1=0, X equals A1 & A2.
    check_B1_zero_makes_output_and: assert property (
        @(posedge CLK) (B1 == 1'b0) |=> (X == (A1 & A2))
    );

    // When B1=0 and A1=1, X equals A2.
    check_B1_zero_A1_one_output_equals_A2: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (A1 == 1'b1)) |=> (X == A2)
    );

    // When B1=0 and A2=1, X equals A1.
    check_B1_zero_A2_one_output_equals_A1: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (A2 == 1'b1)) |=> (X == A1)
    );

    // When (A1&A2)=0, X equals B1.
    check_and_zero_makes_output_equal_B1: assert property (
        @(posedge CLK) !(A1 && A2) |=> (X == B1)
    );

    // When B1=0 and X=1, then (A1&A2)=1.
    check_B1_zero_output_one_requires_and: assert property (
        @(posedge CLK) ((B1 == 1'b0) && (X == 1'b1)) |=> (A1 && A2)
    );
endmodule