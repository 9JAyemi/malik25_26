module four_input_and_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X
);
    // No clock/reset in DUT; purely combinational; sample on any input/output edge.

    // Combinational equivalence: X equals A1 & A2 & B1 & C1.
    check_and_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            X == (A1 & A2 & B1 & C1)
    );

    // X high only if all inputs are high.
    check_x_implies_all_ones: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            X |-> (A1 && A2 && B1 && C1)
    );

    // All inputs high imply X is high.
    check_all_ones_implies_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (A1 && A2 && B1 && C1) |-> X
    );

    // A1 low forces X low.
    check_a1_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (!A1) |-> (X == 1'b0)
    );

    // A2 low forces X low.
    check_a2_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (!A2) |-> (X == 1'b0)
    );

    // B1 low forces X low.
    check_b1_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (!B1) |-> (X == 1'b0)
    );

    // C1 low forces X low.
    check_c1_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (!C1) |-> (X == 1'b0)
    );

    // X rising implies all inputs are high now.
    check_rose_x_requires_all_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            $rose(X) |-> (A1 && A2 && B1 && C1)
    );

    // X falling implies at least one input is low now.
    check_fell_x_requires_any_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            $fell(X) |-> (!A1 || !A2 || !B1 || !C1)
    );

    // If inputs are unchanged since last sample, X is unchanged (combinational determinism).
    check_stability_with_stable_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge X or negedge X)
            (A1 == $past(A1) && A2 == $past(A2) && B1 == $past(B1) && C1 == $past(C1)) |-> (X == $past(X))
    );
endmodule