module logic_circuit_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [3:0] out
);

    // out[0] is the OR reduction of the lower nibble.
    check_lower_or: assert property (
        @(posedge clk) out[0] == (|in[3:0])
    );

    // out[1] is the AND reduction of the lower nibble.
    check_lower_and: assert property (
        @(posedge clk) out[1] == (&in[3:0])
    );

    // out[2] is the OR reduction of the upper nibble.
    check_upper_or: assert property (
        @(posedge clk) out[2] == (|in[7:4])
    );

    // out[3] is the AND reduction of the upper nibble.
    check_upper_and: assert property (
        @(posedge clk) out[3] == (&in[7:4])
    );

endmodule