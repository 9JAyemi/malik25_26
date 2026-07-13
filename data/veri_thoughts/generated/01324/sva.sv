module sky130_fd_sc_ms__or2_sva (
    input logic X,
    input logic A,
    input logic B
);
    // OR functionality: X equals A OR B at any input/output edge.
    check_or_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) (X == (A | B))
    );

    // If both inputs are 0, output must be 0.
    check_inputs_zero_imply_x_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

    // If A is 1, output must be 1.
    check_a_one_implies_x_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) (A == 1'b1) |-> (X == 1'b1)
    );

    // If B is 1, output must be 1.
    check_b_one_implies_x_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) (B == 1'b1) |-> (X == 1'b1)
    );

    // If X is 1, at least one input must be 1.
    check_x_one_implies_some_input_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) (X == 1'b1) |-> ((A == 1'b1) || (B == 1'b1))
    );

    // If X is 0, both inputs must be 0.
    check_x_zero_implies_inputs_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0))
    );

    // On X rising edge, at least one input must be 1.
    check_x_rise_requires_input_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) $rose(X) |-> ((A == 1'b1) || (B == 1'b1))
    );

    // On X falling edge, both inputs must be 0.
    check_x_fall_requires_inputs_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) $fell(X) |-> ((A == 1'b0) && (B == 1'b0))
    );

    // If A falls while B is 0, X must be 0.
    check_a_fall_with_b_zero_implies_x_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) ($fell(A) && (B == 1'b0)) |-> (X == 1'b0)
    );

    // If B falls while A is 0, X must be 0.
    check_b_fall_with_a_zero_implies_x_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) ($fell(B) && (A == 1'b0)) |-> (X == 1'b0)
    );
endmodule