module top_module_sva (
    input logic CLK,
    input logic [15:0] in,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out,
    input logic [15:0] mult_out,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo,
    input logic [7:0] add_out,
    input logic overflow
);
    ///// Multiplication module /////
    // mult_out equals a * b.
    check_mult_out_equals_product: assert property (
        @(posedge CLK) mult_out == (a * b)
    );

    ///// Byte splitter module /////
    // out_hi equals upper byte of mult_out.
    check_out_hi_equals_upper_byte: assert property (
        @(posedge CLK) out_hi == mult_out[15:8]
    );
    // out_lo equals lower byte of mult_out.
    check_out_lo_equals_lower_byte: assert property (
        @(posedge CLK) out_lo == mult_out[7:0]
    );

    ///// Add/overflow detection module /////
    // {overflow, add_out} equals a + b.
    check_add_out_equals_sum: assert property (
        @(posedge CLK) {overflow, add_out} == (a + b)
    );
    // add_out equals lower 8 bits of a + b.
    check_add_out_lower_bits: assert property (
        @(posedge CLK) add_out == (a + b)[7:0]
    );
    // overflow equals MSB of a + b.
    check_overflow_msb: assert property (
        @(posedge CLK) overflow == (a + b)[8]
    );

    ///// Top-level wiring /////
    // out equals add_out.
    check_out_equals_add_out: assert property (
        @(posedge CLK) out == add_out
    );
    // out_hi equals upper byte of mult_out.
    check_out_hi_equals_upper_byte: assert property (
        @(posedge CLK) out_hi == mult_out[15:8]
    );
    // out_lo equals lower byte of mult_out.
    check_out_lo_equals_lower_byte: assert property (
        @(posedge CLK) out_lo == mult_out[7:0]
    );
    // out equals upper byte of mult_out.
    check_out_equals_upper_byte: assert property (
        @(posedge CLK) out == mult_out[15:8]
    );
    // out equals a + b (via add_out).
    check_out_equals_sum: assert property (
        @(posedge CLK) out == (a + b)[7:0]
    );
    // overflow equals MSB of a + b.
    check_overflow_equals_msb: assert property (
        @(posedge CLK) overflow == (a + b)[8]
    );
endmodule