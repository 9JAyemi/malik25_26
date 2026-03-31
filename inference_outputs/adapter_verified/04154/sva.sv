module invert_msb_sva (
    input logic clk,
    input logic [3:0] i_binary,
    input logic [3:0] o_inverted
);

// Output MSB is the bitwise inversion of the input MSB.
    check_msb_inversion: assert property (
        @(posedge clk) o_inverted[3] == ~i_binary[3]
    );

// Output bits [2:0] pass through the input bits [2:0].
    check_lsb_passthrough: assert property (
        @(posedge clk) o_inverted[2:0] == i_binary[2:0]
    );

// The full output bus matches the RTL concatenation.
    check_full_output: assert property (
        @(posedge clk) o_inverted == {~i_binary[3], i_binary[2:0]}
    );

endmodule
