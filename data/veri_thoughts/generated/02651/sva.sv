module sky130_fd_sc_hvl__o21a_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);
    // Functional equivalence: X == (A1 | A2) & B1.
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ((A1 | A2) & B1)
    );

    // When B1 is LOW, X must be LOW.
    check_b1_low_forces_x_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // When B1 is HIGH, X equals (A1 | A2).
    check_b1_high_passes_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b1) |-> (X == (A1 | A2))
    );

    // If A1 and B1 are HIGH, X must be HIGH.
    check_a1_and_b1_high_implies_x_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // If A2 and B1 are HIGH, X must be HIGH.
    check_a2_and_b1_high_implies_x_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // If both A1 and A2 are LOW, X must be LOW.
    check_both_a_low_implies_x_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // X can be HIGH only if B1 is HIGH and at least one of A1/A2 is HIGH.
    check_x_high_implies_required_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b1) |-> (B1 == 1'b1) && (((A1 | A2) == 1'b1))
    );

    // With inputs stable across a cycle, X must be stable across the cycle.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A1) && $stable(A2) && $stable(B1)) |-> $stable(X)
    );
endmodule