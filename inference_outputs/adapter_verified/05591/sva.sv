module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);

// No RTL reset; assertions are always active.

    // Output matches the RTL pipeline shift function.
    check_full_pipeline_function: assert property (
        @(posedge clk) out == ((dir == 0) ? ((in << shift) << shift) : ((in >> shift) >> shift))
    );

// A zero shift amount passes the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift == 4'd0) |-> (out == in)
    );

// Left shifts increase the MSB by the total shift amount.
    check_left_shift_msb: assert property (
        @(posedge clk) (dir == 1'b0) |-> (out[15] == in[15 - shift])
    );

// Right shifts increase the LSB by the total shift amount.
    check_right_shift_lsb: assert property (
        @(posedge clk) (dir == 1'b1) |-> (out[0] == in[0 + shift])
    );

// Left shifts zero the vacated lower bits.
    check_left_shift_zero_lower_bits: assert property (
        @(posedge clk) (dir == 1'b0) |-> (out[shift-1:0] == 16'h0000)
    );

// Right shifts zero the vacated upper bits.
    check_right_shift_zero_upper_bits: assert property (
        @(posedge clk) (dir == 1'b1) |-> (out[15:16-shift] == 16'h0000)
    );

// A shift of 15 moves the input bit into bit 0.
    check_max_left_shift_bit_mapping: assert property (
        @(posedge clk) (dir == 1'b0) && (shift == 4'd15) |-> (out[0] == in[15])
    );

// A shift of 15 moves the input bit into bit 15.
    check_max_right_shift_bit_mapping: assert property (
        @(posedge clk) (dir == 1'b1) && (shift == 4'd15) |-> (out[15] == in[0])
    );

endmodule
