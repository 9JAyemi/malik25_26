module my_mux2_assertions (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic S
);

    // X matches the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) X == ((A0 & ~S) | (A1 & S))
    );

    // When S is low, X selects A0.
    check_select_a0_when_s_low: assert property (
        @(posedge clk) (S == 1'b0) |-> (X == A0)
    );

    // When S is high, X selects A1.
    check_select_a1_when_s_high: assert property (
        @(posedge clk) (S == 1'b1) |-> (X == A1)
    );

    // If both data inputs are low, X is low.
    check_output_low_when_both_inputs_low: assert property (
        @(posedge clk) ((A0 == 1'b0) && (A1 == 1'b0)) |-> (X == 1'b0)
    );

    // If both data inputs are high, X is high.
    check_output_high_when_both_inputs_high: assert property (
        @(posedge clk) ((A0 == 1'b1) && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // If both data inputs match, X equals that common value.
    check_output_matches_common_input: assert property (
        @(posedge clk) (A0 == A1) |-> (X == A0)
    );

    // With A0 low and A1 high, X follows S.
    check_output_follows_s_for_01_inputs: assert property (
        @(posedge clk) ((A0 == 1'b0) && (A1 == 1'b1)) |-> (X == S)
    );

    // With A0 high and A1 low, X follows inverted S.
    check_output_follows_not_s_for_10_inputs: assert property (
        @(posedge clk) ((A0 == 1'b1) && (A1 == 1'b0)) |-> (X == ~S)
    );

endmodule