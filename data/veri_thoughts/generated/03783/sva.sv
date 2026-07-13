module ring_counter_shift_register_decoder_mux_sva (
    input logic        clk,
    input logic        d,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // Clock is clk; the RTL has no reset.
    
    // d history 00 selects no output.
    check_decode_00_outputs_zero: assert property (
        @(posedge clk)
        (($past(d,3) === 1'b0) && ($past(d,2) === 1'b0))
        |-> ((out_hi == 8'b0) && (out_lo == 8'b0))
    );

    // d history 01 drives the upper input byte to out_hi.
    check_decode_01_routes_upper_byte: assert property (
        @(posedge clk)
        (($past(d,3) === 1'b0) && ($past(d,2) === 1'b1))
        |-> ((out_hi == in[15:8]) && (out_lo == 8'b0))
    );

    // d history 10 drives the lower input byte to out_lo.
    check_decode_10_routes_lower_byte: assert property (
        @(posedge clk)
        (($past(d,3) === 1'b1) && ($past(d,2) === 1'b0))
        |-> ((out_hi == 8'b0) && (out_lo == in[7:0]))
    );

    // d history 11 selects no output.
    check_decode_11_outputs_zero: assert property (
        @(posedge clk)
        (($past(d,3) === 1'b1) && ($past(d,2) === 1'b1))
        |-> ((out_hi == 8'b0) && (out_lo == 8'b0))
    );

    // out_hi is always either zero or the upper input byte.
    check_out_hi_is_zero_or_upper_byte: assert property (
        @(posedge clk)
        ((out_hi == 8'b0) || (out_hi == in[15:8]))
    );

    // out_lo is always either zero or the lower input byte.
    check_out_lo_is_zero_or_lower_byte: assert property (
        @(posedge clk)
        ((out_lo == 8'b0) || (out_lo == in[7:0]))
    );

    // A nonzero out_hi requires out_lo to be zero.
    check_nonzero_out_hi_excludes_out_lo: assert property (
        @(posedge clk)
        (out_hi != 8'b0) |-> (out_lo == 8'b0)
    );

    // A nonzero out_lo requires out_hi to be zero.
    check_nonzero_out_lo_excludes_out_hi: assert property (
        @(posedge clk)
        (out_lo != 8'b0) |-> (out_hi == 8'b0)
    );

endmodule