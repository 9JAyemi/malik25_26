module multiplier_block_sva (
    input logic        clk,
    input logic [31:0] i_data0,
    input logic [31:0] o_data0
);

    // Output matches the RTL shift/subtract implementation.
    check_output_chain: assert property (
        @(posedge clk)
        o_data0 == (((((i_data0 << 2) - i_data0) << 7) - i_data0) << 2)
    );

    // Output also matches the equivalent 1532*x shift/add form.
    check_output_simplified: assert property (
        @(posedge clk)
        o_data0 == ((i_data0 << 10) + (i_data0 << 9) - (i_data0 << 2))
    );

    // Final left shift by 2 forces the two LSBs low.
    check_output_low_bits_zero: assert property (
        @(posedge clk)
        o_data0[1:0] == 2'b00
    );

    // Zero input must produce zero output.
    check_zero_input_zero_output: assert property (
        @(posedge clk)
        (i_data0 == 32'h00000000) |-> (o_data0 == 32'h00000000)
    );

    // Inputs divisible by 4 produce outputs divisible by 16.
    check_input_multiple_of_4_output_multiple_of_16: assert property (
        @(posedge clk)
        (i_data0[1:0] == 2'b00) |-> (o_data0[3:0] == 4'b0000)
    );

    // Inputs with only the top two bits set map to zero.
    check_top_bits_only_input_zero_output: assert property (
        @(posedge clk)
        (i_data0[29:0] == 30'b0) |-> (o_data0 == 32'h00000000)
    );

endmodule