module twos_complement_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b
);

    // Output equals the 4-bit two's complement of the input.
    check_output_twos_complement: assert property (
        @(posedge clk) b == ((~a) + 4'd1)
    );

    // Input and output sum to zero modulo 16.
    check_additive_inverse_mod16: assert property (
        @(posedge clk) (a + b) == 4'd0
    );

    // Zero remains unchanged by two's complement.
    check_zero_fixed_point: assert property (
        @(posedge clk) (a == 4'd0) |-> (b == 4'd0)
    );

    // 4'b1000 remains unchanged in 4-bit two's complement.
    check_most_negative_fixed_point: assert property (
        @(posedge clk) (a == 4'b1000) |-> (b == 4'b1000)
    );

endmodule