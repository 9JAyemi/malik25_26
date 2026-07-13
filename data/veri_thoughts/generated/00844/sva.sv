module and_or_gate_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // X equals A1&A2&(A3|B1|B2).
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ((A1 & A2) & (A3 | B1 | B2))
    );

    // If X is 1 then A1 must be 1.
    check_x_implies_a1: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> A1
    );

    // If X is 1 then A2 must be 1.
    check_x_implies_a2: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> A2
    );

    // If X is 1 then at least one of A3/B1/B2 must be 1.
    check_x_implies_or: assert property (
        @(posedge CLK) disable iff (!RESETn) X |-> (A3 | B1 | B2)
    );

    // If A1 is 0 then X must be 0.
    check_zero_when_a1_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A1) |-> (X == 1'b0)
    );

    // If A2 is 0 then X must be 0.
    check_zero_when_a2_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A2) |-> (X == 1'b0)
    );

    // If A3,B1,B2 are all 0 then X must be 0.
    check_zero_when_or_inputs_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A3 & !B1 & !B2) |-> (X == 1'b0)
    );

    // If A1&A2 and any of A3/B1/B2 then X must be 1.
    check_one_when_and_and_any_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 & A2 & (A3 | B1 | B2)) |-> (X == 1'b1)
    );

    // If A1&A2 and none of A3/B1/B2 then X must be 0.
    check_zero_when_and_and_no_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 & A2 & !A3 & !B1 & !B2) |-> (X == 1'b0)
    );

    // When A1&A2 are 1, X equals (A3|B1|B2).
    check_a1a2_high_means_x_matches_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 & A2) |-> (X == (A3 | B1 | B2))
    );

    // When any of A3/B1/B2 is 1, X equals (A1&A2).
    check_or_high_means_x_matches_and: assert property (
        @(posedge CLK) disable iff (!RESETn) (A3 | B1 | B2) |-> (X == (A1 & A2))
    );
endmodule