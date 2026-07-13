module top_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // X equals (A1|A2|A3)&B1&C1 at any input edge.
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        X == ((A1 | A2 | A3) & B1 & C1)
    );

    // If B1 is LOW, X must be LOW.
    check_zero_when_B1_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If C1 is LOW, X must be LOW.
    check_zero_when_C1_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (C1 == 1'b0) |-> (X == 1'b0)
    );

    // If all A inputs are LOW, X must be LOW.
    check_zero_when_all_A_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );

    // With B1&C1 HIGH and A1 HIGH, X must be HIGH.
    check_one_when_A1_and_gates_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 == 1'b1) && (C1 == 1'b1) && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // With B1&C1 HIGH and A2 HIGH, X must be HIGH.
    check_one_when_A2_and_gates_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 == 1'b1) && (C1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // With B1&C1 HIGH and A3 HIGH, X must be HIGH.
    check_one_when_A3_and_gates_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 == 1'b1) && (C1 == 1'b1) && (A3 == 1'b1)) |-> (X == 1'b1)
    );

    // When B1&C1 are HIGH, X equals A1|A2|A3.
    check_when_gates_high_output_matches_or: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 == 1'b1) && (C1 == 1'b1)) |-> (X == (A1 | A2 | A3))
    );

    // X HIGH implies B1&C1 HIGH and at least one A HIGH.
    check_x_high_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (X == 1'b1) |-> ((B1 == 1'b1) && (C1 == 1'b1) && ((A1 | A2 | A3) == 1'b1))
    );

    // With B1&C1 HIGH and all A LOW, X must be LOW.
    check_zero_when_gates_high_and_as_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 == 1'b1) && (C1 == 1'b1) && ((A1 | A2 | A3) == 1'b0)) |-> (X == 1'b0)
    );
endmodule