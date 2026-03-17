module MUX_2_TO_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Z
);

    // Output must implement the mux equation.
    check_mux_function: assert property (
        @(posedge clk) Z === ((S == 1'b0) ? A : B)
    );

    // Low select routes A to the output.
    check_select_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Z === A)
    );

    // High select routes B to the output.
    check_select_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Z === B)
    );

    // If both inputs match, the output must match them as well.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A === B) |-> (Z === A)
    );

endmodule