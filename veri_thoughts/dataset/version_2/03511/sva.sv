module mux2_sva #(
    parameter int bitwidth = 32
) (
    input logic clk,
    input logic sel,
    input logic [bitwidth-1:0] a,
    input logic [bitwidth-1:0] b,
    input logic [bitwidth-1:0] y
);

    // Output always matches the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) y == (sel ? b : a)
    );

    // When select is low, output must equal input a.
    check_select_a_path: assert property (
        @(posedge clk) !sel |-> (y == a)
    );

    // When select is high, output must equal input b.
    check_select_b_path: assert property (
        @(posedge clk) sel |-> (y == b)
    );

    // If both inputs are equal, output must equal that common value.
    check_equal_inputs: assert property (
        @(posedge clk) (a == b) |-> (y == a)
    );

    // Output must always match one of the two inputs.
    check_output_matches_an_input: assert property (
        @(posedge clk) (y == a) || (y == b)
    );

endmodule