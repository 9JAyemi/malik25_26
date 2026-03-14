module bitwise_and_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X
);
    // X equals A1 & A2 & B1 on any input transition.
    check_and_equation_on_input_edges: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (X == (A1 & A2 & B1))
    );

    // X equals A1 & A2 & B1 whenever X toggles.
    check_and_equation_on_output_edges: assert property (
        @(posedge X or negedge X)
        (X == (A1 & A2 & B1))
    );

    // X rising implies all inputs are HIGH.
    check_x_rise_requires_all_inputs_high: assert property (
        @(posedge X)
        (A1 && A2 && B1)
    );

    // X falling implies at least one input is LOW.
    check_x_fall_requires_some_input_low: assert property (
        @(negedge X)
        (!A1 || !A2 || !B1)
    );

    // If A1 is LOW, X must be LOW (sampled on A1 edges).
    check_a1_low_forces_x_low: assert property (
        @(posedge A1 or negedge A1)
        (A1 == 1'b0) |-> (X == 1'b0)
    );

    // If A2 is LOW, X must be LOW (sampled on A2 edges).
    check_a2_low_forces_x_low: assert property (
        @(posedge A2 or negedge A2)
        (A2 == 1'b0) |-> (X == 1'b0)
    );

    // If B1 is LOW, X must be LOW (sampled on B1 edges).
    check_b1_low_forces_x_low: assert property (
        @(posedge B1 or negedge B1)
        (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If all inputs are HIGH, X must be HIGH (on any input edge).
    check_all_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (A1 && A2 && B1) |-> (X == 1'b1)
    );
endmodule