module top_module_sva (
    input logic clk,
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

// out_and is the reduction AND of in.
    check_and_function: assert property (
        @(posedge clk) out_and == (&in)
    );

// out_or is the reduction OR of in.
    check_or_function: assert property (
        @(posedge clk) out_or == (|in)
    );

// out_xor is the reduction XOR of in.
    check_xor_function: assert property (
        @(posedge clk) out_xor == (^in)
    );

// out_and and out_or are never both HIGH together.
    check_and_or_mutex: assert property (
        @(posedge clk) !(out_and && out_or)
    );

// If in is all zeros, out_and and out_xor are LOW and out_or is HIGH.
    check_zero_input_behavior: assert property (
        @(posedge clk) (in == 100'b0) |-> (!out_and && !out_xor && out_or)
    );

// If in is all ones, out_and and out_or are HIGH and out_xor is LOW.
    check_all_ones_input_behavior: assert property (
        @(posedge clk) (in == 100'b1) |-> (out_and && out_or && !out_xor)
    );

// If in has exactly one HIGH bit, out_and is LOW, out_or is HIGH, and out_xor is HIGH.
    check_single_one_input_behavior: assert property (
        @(posedge clk) $onehot(in) |-> (!out_and && out_or && out_xor)
    );

// If in has exactly two HIGH bits, out_and is LOW, out_or is HIGH, and out_xor is LOW.
    check_two_ones_input_behavior: assert property (
        @(posedge clk) $onehot0(in) |-> (!out_and && out_or && !out_xor)
    );

endmodule
