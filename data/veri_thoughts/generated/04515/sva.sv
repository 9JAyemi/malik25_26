module Span12Mux_v11_sva (
    input logic        clk,
    input logic [11:0] I,
    input logic        O
);

    // Output matches the RTL mux expression.
    check_output_equation: assert property (
        @(posedge clk) (O == (I[11] ? I[10] : I[11]))
    );

    // Output is low whenever I[11] is low.
    check_output_low_when_i11_low: assert property (
        @(posedge clk) (!I[11]) |-> (!O)
    );

    // Output follows I[10] whenever I[11] is high.
    check_output_follows_i10_when_i11_high: assert property (
        @(posedge clk) I[11] |-> (O == I[10])
    );

    // A high output requires both I[11] and I[10] to be high.
    check_output_high_requires_top_bits_high: assert property (
        @(posedge clk) O |-> (I[11] && I[10])
    );

    // Both top input bits high force the output high.
    check_output_high_when_top_bits_high: assert property (
        @(posedge clk) (I[11] && I[10]) |-> O
    );

endmodule