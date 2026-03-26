module mux_2to1_sva (
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic        sel,
    input logic [15:0] mux_out
);

    // Combinational mux with no RTL clock or reset; sample on $global_clock.

    // If sel compares equal to 0, the upper byte of mux_out comes from a.
    check_sel_zero_upper_byte_from_a: assert property (
        @($global_clock) (sel === 1'b0) |-> (mux_out[15:8] == a)
    );

    // If sel compares equal to 0, the lower byte of mux_out is zero.
    check_sel_zero_lower_byte_zero: assert property (
        @($global_clock) (sel === 1'b0) |-> (mux_out[7:0] == 8'b0)
    );

    // If sel does not compare equal to 0, the upper byte of mux_out is zero.
    check_sel_nonzero_upper_byte_zero: assert property (
        @($global_clock) (sel !== 1'b0) |-> (mux_out[15:8] == 8'b0)
    );

    // If sel does not compare equal to 0, the lower byte of mux_out comes from b.
    check_sel_nonzero_lower_byte_from_b: assert property (
        @($global_clock) (sel !== 1'b0) |-> (mux_out[7:0] == b)
    );

endmodule