module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [3:0] in1_hi,
    input logic [3:0] in1_lo,
    input logic [3:0] in2_hi,
    input logic [3:0] in2_lo,
    input logic [7:0] out
);

    // in1_hi is the upper nibble of the upper input byte.
    check_in1_hi_slice: assert property (
        @(posedge clk) in1_hi == in[15:12]
    );

    // in1_lo is the lower nibble of the upper input byte.
    check_in1_lo_slice: assert property (
        @(posedge clk) in1_lo == in[11:8]
    );

    // in2_hi is the upper nibble of the lower input byte.
    check_in2_hi_slice: assert property (
        @(posedge clk) in2_hi == in[7:4]
    );

    // in2_lo is the lower nibble of the lower input byte.
    check_in2_lo_slice: assert property (
        @(posedge clk) in2_lo == in[3:0]
    );

    // out upper nibble is always zero from zero-extension of the 4-bit sum.
    check_out_upper_nibble_zero: assert property (
        @(posedge clk) out[7:4] == 4'h0
    );

    // out lower nibble is the truncated sum of the two absolute nibble differences.
    check_out_lower_nibble_absdiff_sum: assert property (
        @(posedge clk)
        out[3:0] ==
            (((in[15:12] >= in[7:4]) ? (in[15:12] - in[7:4]) : (in[7:4] - in[15:12])) +
             ((in[11:8]  >= in[3:0]) ? (in[11:8]  - in[3:0]) : (in[3:0]  - in[11:8])))
    );

    // Equal upper and lower bytes produce a zero output.
    check_equal_bytes_zero_out: assert property (
        @(posedge clk) (in[15:8] == in[7:0]) |-> (out == 8'h00)
    );

    // If the high nibbles match, only the low-nibble absolute difference remains.
    check_equal_high_nibbles_reduce_to_low_diff: assert property (
        @(posedge clk)
        (in[15:12] == in[7:4]) |->
            (out[3:0] == ((in[11:8] >= in[3:0]) ? (in[11:8] - in[3:0]) : (in[3:0] - in[11:8])))
    );

    // If the low nibbles match, only the high-nibble absolute difference remains.
    check_equal_low_nibbles_reduce_to_high_diff: assert property (
        @(posedge clk)
        (in[11:8] == in[3:0]) |->
            (out[3:0] == ((in[15:12] >= in[7:4]) ? (in[15:12] - in[7:4]) : (in[7:4] - in[15:12])))
    );

endmodule