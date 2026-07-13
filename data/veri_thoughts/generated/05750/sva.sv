module mux_2_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Output matches the mux select function.
    check_mux_function: assert property (
        @(posedge clk) Y == (SEL ? B : A)
    );

    // When select is low, the output routes A.
    check_sel_low_routes_a: assert property (
        @(posedge clk) !SEL |-> (Y == A)
    );

    // When select is high, the output routes B.
    check_sel_high_routes_b: assert property (
        @(posedge clk) SEL |-> (Y == B)
    );

    // The output is always equal to one of the two inputs.
    check_output_is_input_a_or_b: assert property (
        @(posedge clk) (Y == A) || (Y == B)
    );

    // If both inputs match, the output matches that value.
    check_equal_inputs_produce_same_output: assert property (
        @(posedge clk) (A == B) |-> (Y == A)
    );

    // If output differs from A, B must be selected and drive the output.
    check_output_differs_from_a_only_when_b_selected: assert property (
        @(posedge clk) (Y != A) |-> (SEL && (Y == B))
    );

    // If output differs from B, A must be selected and drive the output.
    check_output_differs_from_b_only_when_a_selected: assert property (
        @(posedge clk) (Y != B) |-> ((!SEL) && (Y == A))
    );

endmodule