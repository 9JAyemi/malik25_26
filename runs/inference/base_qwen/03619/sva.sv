module binary_decoder_3to8_sva (
    input logic clk,
    input logic rst_n,
    input logic [2:0] in,
    output logic [7:0] out
);
    // Combinational logic, so use @(posedge clk)
    // Reset is active low

    // Output should be 0 when reset is active
    reset_output: assert property (
        @(posedge clk) disable iff (!rst_n) (out == 8'b00000000)
    );

    // Output should be one-hot encoded based on input
    one_hot_output: assert property (
        @(posedge clk) disable iff (!rst_n) (
            (in == 3'b000 && out == 8'b00000001) ||
            (in == 3'b001 && out == 8'b00000010) ||
            (in == 3'b010 && out == 8'b00000100) ||
            (in == 3'b011 && out == 8'b00001000) ||
            (in == 3'b100 && out == 8'b00010000) ||
            (in == 3'b101 && out == 8'b00100000) ||
            (in == 3'b110 && out == 8'b01000000) ||
            (in == 3'b111 && out == 8'b10000000)
        )
    );

    // Default case should not be reached
    default_case: assert property (
        @(posedge clk) disable iff (!rst_n) (in != 3'b111 || out == 8'b00000000)
    );

endmodule