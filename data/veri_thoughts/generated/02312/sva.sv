module comb_op_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);
    // Out equals left shift for inputs 0..7.
    check_left_shift_range_eq: assert property (
        @(posedge clk) disable iff (1'b0) (in <= 4'd7) |-> (out == (in << 1))
    );

    // Out equals right shift for inputs 8..15.
    check_right_shift_range_eq: assert property (
        @(posedge clk) disable iff (1'b0) (in >= 4'd8) |-> (out == (in >> 1))
    );

    // Piecewise definition matches MSB: 0 => left shift, 1 => right shift.
    check_piecewise_functionality: assert property (
        @(posedge clk) disable iff (1'b0) out == (in[3] ? (in >> 1) : (in << 1))
    );

    // LSB is zero when left shifting (in <= 7).
    check_left_shift_lsb_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in <= 4'd7) |-> (out[0] == 1'b0)
    );

    // MSB is zero when right shifting (in >= 8).
    check_right_shift_msb_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in >= 4'd8) |-> (out[3] == 1'b0)
    );

    // Left shift moves bits up by one (out[3:1] = in[2:0]) for in <= 7.
    check_left_shift_bit_move: assert property (
        @(posedge clk) disable iff (1'b0) (in <= 4'd7) |-> (out[3:1] == in[2:0])
    );

    // Right shift moves bits down by one (out[2:0] = in[3:1]) for in >= 8.
    check_right_shift_bit_move: assert property (
        @(posedge clk) disable iff (1'b0) (in >= 4'd8) |-> (out[2:0] == in[3:1])
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) disable iff (1'b0) (in == 4'd0) |-> (out == 4'd0)
    );

    // Maximum value 15 maps to 7 (15 >> 1).
    check_fifteen_maps_to_seven: assert property (
        @(posedge clk) disable iff (1'b0) (in == 4'd15) |-> (out == 4'd7)
    );
endmodule