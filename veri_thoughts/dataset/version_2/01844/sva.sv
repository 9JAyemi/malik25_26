module three_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic Y,
    input logic VPWR,
    input logic VGND
);
    // Y matches the boolean function encoded in the RTL.
    check_function_equivalence: assert property (
        @(posedge VPWR) Y == ((A1 && A2) || ((!A1) && (!A2) && (!B1_N)))
    );

    // When both A1 and A2 are HIGH, Y is HIGH.
    check_both_high_sets_y: assert property (
        @(posedge VPWR) (A1 && A2) |-> (Y == 1'b1)
    );

    // When exactly one of A1/A2 is HIGH, Y is LOW.
    check_one_hot_clears_y: assert property (
        @(posedge VPWR) (A1 ^ A2) |-> (Y == 1'b0)
    );

    // When both A1 and A2 are LOW and B1_N is LOW, Y is HIGH.
    check_both_low_b1n_low_sets_y: assert property (
        @(posedge VPWR) (!A1 && !A2 && !B1_N) |-> (Y == 1'b1)
    );

    // When both A1 and A2 are LOW and B1_N is HIGH, Y is LOW.
    check_both_low_b1n_high_clears_y: assert property (
        @(posedge VPWR) (!A1 && !A2 && B1_N) |-> (Y == 1'b0)
    );

    // With B1_N HIGH, Y equals A1 AND A2.
    check_b1n_high_reduces_to_and: assert property (
        @(posedge VPWR) (B1_N == 1'b1) |-> (Y == (A1 && A2))
    );

    // With B1_N LOW, Y equals XNOR of A1 and A2.
    check_b1n_low_reduces_to_xnor: assert property (
        @(posedge VPWR) (B1_N == 1'b0) |-> (Y == ~(A1 ^ A2))
    );

    // If A1, A2, and B1_N are stable, Y remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge VPWR) ($stable(A1) && $stable(A2) && $stable(B1_N)) |-> $stable(Y)
    );

    // Y can be HIGH only for the allowed input combinations.
    check_y_high_implies_valid_inputs: assert property (
        @(posedge VPWR) (Y == 1'b1) |-> ((A1 && A2) || (!A1 && !A2 && !B1_N))
    );
endmodule