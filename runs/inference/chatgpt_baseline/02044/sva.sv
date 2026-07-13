module sky130_fd_sc_hvl__a22o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // X equals (A1 & A2) OR (B1 & B2).
    check_function_equation: assert property (
        @(posedge $global_clock) X == ((A1 & A2) | (B1 & B2))
    );

    // If A pair both HIGH, X must be HIGH.
    check_high_when_A_pair_high: assert property (
        @(posedge $global_clock) (A1 & A2) |-> (X == 1'b1)
    );

    // If B pair both HIGH, X must be HIGH.
    check_high_when_B_pair_high: assert property (
        @(posedge $global_clock) (B1 & B2) |-> (X == 1'b1)
    );

    // If neither pair is both HIGH, X must be LOW.
    check_low_when_no_pair_high: assert property (
        @(posedge $global_clock) (!(A1 & A2) && !(B1 & B2)) |-> (X == 1'b0)
    );

    // If X is HIGH, at least one pair is both HIGH.
    check_X_high_implies_some_pair_high: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> ((A1 & A2) || (B1 & B2))
    );

    // With inputs stable, X must remain stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge $global_clock) ($stable(A1) && $stable(A2) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );
endmodule