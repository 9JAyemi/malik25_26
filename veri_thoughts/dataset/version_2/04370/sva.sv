module even_odd_assertions (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // The sampled output matches the implemented parity-based mapping.
    check_output_function: assert property (
        @(posedge clk) out == (in[0] ? in[2:1] : 2'b00)
    );

    // Even inputs take the multiply-by-2 branch, which truncates to 2'b00.
    check_even_input_output_zero: assert property (
        @(posedge clk) !in[0] |-> (out == 2'b00)
    );

    // Odd inputs take the divide-by-2 branch and return input bits [2:1].
    check_odd_input_divide_result: assert property (
        @(posedge clk) in[0] |-> (out == in[2:1])
    );

    // The lowest input value maps to zero.
    check_zero_input_output_zero: assert property (
        @(posedge clk) (in == 4'h0) |-> (out == 2'b00)
    );

    // The highest odd input value maps to the truncated quotient 2'b11.
    check_max_input_output_three: assert property (
        @(posedge clk) (in == 4'hF) |-> (out == 2'b11)
    );

endmodule