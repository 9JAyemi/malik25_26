module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // No clock/reset in RTL; combinational; sample on input posedges.

    // Canonical Boolean equality for X.
    check_canonical_equation: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (X == ((!B1) & (A2 & (A1 | A3))))
    );

    // When B1 is HIGH, X must be 0.
    check_b1_forces_zero: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        B1 |-> (X == 1'b0)
    );

    // When B1 is LOW, X equals (A1&A2)|(A2&A3).
    check_b1_low_function: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1) |-> (X == ((A1 & A2) | (A2 & A3)))
    );

    // With B1 LOW and A2 LOW, X must be 0.
    check_a2_zero_forces_zero: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && !A2) |-> (X == 1'b0)
    );

    // With B1 LOW and A2&A1 HIGH, X must be 1.
    check_a1_a2_set_x: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && A1 && A2) |-> (X == 1'b1)
    );

    // With B1 LOW and A2&A3 HIGH, X must be 1.
    check_a2_a3_set_x: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && A2 && A3) |-> (X == 1'b1)
    );

    // With B1 LOW, A2 HIGH, and A1/A3 both LOW, X must be 0.
    check_no_neighbors_zero: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && A2 && !A1 && !A3) |-> (X == 1'b0)
    );

    // If X is 1, then B1 must be LOW and A2=1 and (A1 or A3)=1.
    check_x_one_implies_inputs: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        X |-> (!B1 && A2 && (A1 || A3))
    );

    // With B1 LOW and A2 LOW even if A1 or A3 is HIGH, X must be 0.
    check_a2_gating_effect: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && !A2 && (A1 || A3)) |-> (X == 1'b0)
    );

    // With B1 LOW and A2 HIGH and exactly one of A1/A3 HIGH, X must be 1.
    check_single_neighbor_sets_x: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1)
        (!B1 && A2 && (A1 ^ A3)) |-> (X == 1'b1)
    );

endmodule