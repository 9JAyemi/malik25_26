module final_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [15:0] out
);

// Upper byte is a direct copy of the input upper byte.
    check_upper_byte_passthrough: assert property (
        @(posedge clk) out[15:8] == in[15:8]
    );

// Lower byte is a direct copy of the input lower byte.
    check_lower_byte_passthrough: assert property (
        @(posedge clk) out[7:0] == in[7:0]
    );

// Output bit 0 is the AND of the two input LSBs.
    check_bit0_and_function: assert property (
        @(posedge clk) out[0] == (in[0] & in[7])
    );

// Output bits [15:1] are a direct copy of the input.
    check_upper_bits_passthrough: assert property (
        @(posedge clk) out[15:1] == in[15:1]
    );

endmodule
