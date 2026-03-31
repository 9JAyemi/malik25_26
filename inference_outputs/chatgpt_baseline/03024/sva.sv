module mode_selector_sva (
    input logic clk,
    input logic [1:0] mode,
    input logic [3:0] in,
    input logic [3:0] out
);

    // Mode 00 left-shifts input and zero-fills the LSB.
    check_mode_shift_left: assert property (
        @(posedge clk) (mode == 2'b00) |-> (out == {in[2:0], 1'b0})
    );

    // Mode 01 right-shifts input and zero-fills the MSB.
    check_mode_shift_right: assert property (
        @(posedge clk) (mode == 2'b01) |-> (out == {1'b0, in[3:1]})
    );

    // Mode 10 bitwise-inverts the input.
    check_mode_invert: assert property (
        @(posedge clk) (mode == 2'b10) |-> (out == ~in)
    );

    // Mode 11 passes the input through unchanged.
    check_mode_passthrough: assert property (
        @(posedge clk) (mode == 2'b11) |-> (out == in)
    );

endmodule