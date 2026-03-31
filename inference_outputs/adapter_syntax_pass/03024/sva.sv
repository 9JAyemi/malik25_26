module mode_selector_sva (
    input logic [1:0] mode,
    input logic [3:0] in,
    input logic [3:0] out
);

    // Mode 00 shifts in left and inserts 0 in bit 0.
    check_mode_00_shift_left: assert property (
        @($global_clock) (mode == 2'b00) |-> (out == {in[2:0], 1'b0})
    );

    // Mode 01 shifts in right and inserts 0 in bit 3.
    check_mode_01_shift_right: assert property (
        @($global_clock) (mode == 2'b01) |-> (out == {1'b0, in[3:1]})
    );

    // Mode 10 inverts all input bits.
    check_mode_10_invert: assert property (
        @($global_clock) (mode == 2'b10) |-> (out == ~in)
    );

    // Mode 11 passes the input through unchanged.
    check_mode_11_passthrough: assert property (
        @($global_clock) (mode == 2'b11) |-> (out == in)
    );

    // Default case drives all output bits low.
    check_default_zero: assert property (
        @($global_clock) ((mode != 2'b00) && (mode != 2'b01) && (mode != 2'b10) && (mode != 2'b11)) |-> (out == 4'b0000)
    );

endmodule