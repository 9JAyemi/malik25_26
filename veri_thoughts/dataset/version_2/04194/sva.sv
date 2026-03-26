module twos_comp_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // Output always matches the RTL combinational expression.
    check_out_matches_rtl: assert property (
        @(posedge clk) out == (in[3] ? ((~in) + 4'd1) : in)
    );

    // Non-negative inputs pass through unchanged.
    check_non_negative_passthrough: assert property (
        @(posedge clk) !in[3] |-> (out == in)
    );

    // Inputs with MSB set are converted using two's complement.
    check_negative_twos_complement: assert property (
        @(posedge clk) in[3] |-> (out == ((~in) + 4'd1))
    );

    // For inputs with MSB set, input and output sum to zero modulo 16.
    check_negative_mod16_zero_sum: assert property (
        @(posedge clk) in[3] |-> ((out + in) == 4'd0)
    );

    // The most-negative 4-bit value remains unchanged after two's complement.
    check_min_negative_fixed_point: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 4'b1000)
    );

endmodule