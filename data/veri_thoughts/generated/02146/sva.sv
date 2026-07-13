module barrel_shifter_sva (
    // DUT ports
    input logic [15:0] data_in,
    input logic [3:0]  shift_amount,
    input logic        shift_direction,
    input logic [15:0] data_out,
    // Sampling clock for SVA (DUT has no clock/reset)
    input logic        CLK
);
    // Clocks: none in RTL (assertions sample on CLK). Reset: none. Logic: purely combinational.

    // data_out equals left or right shift of data_in per shift_direction
    check_functional_equation: assert property (
        @(posedge CLK) data_out == (shift_direction ? (data_in >> shift_amount) : (data_in << shift_amount))
    );

    // Zero shift is a passthrough
    check_zero_shift_passthrough: assert property (
        @(posedge CLK) (shift_amount == 4'd0) |-> (data_out == data_in)
    );

    // Left shift by 1 produces {data_in[14:0], 1'b0}
    check_left_shift_by_1: assert property (
        @(posedge CLK) (shift_direction == 1'b0 && shift_amount == 4'd1) |-> (data_out == {data_in[14:0], 1'b0})
    );

    // Right shift by 1 produces {1'b0, data_in[15:1]}
    check_right_shift_by_1: assert property (
        @(posedge CLK) (shift_direction == 1'b1 && shift_amount == 4'd1) |-> (data_out == {1'b0, data_in[15:1]})
    );

    // Left shift by 15 moves bit 0 to MSB and zeros others
    check_left_shift_by_15: assert property (
        @(posedge CLK) (shift_direction == 1'b0 && shift_amount == 4'd15) |-> (data_out == {data_in[0], 15'b0})
    );

    // Right shift by 15 moves MSB to LSB and zeros others
    check_right_shift_by_15: assert property (
        @(posedge CLK) (shift_direction == 1'b1 && shift_amount == 4'd15) |-> (data_out == {15'b0, data_in[15]})
    );

    // Shifting zero always yields zero
    check_zero_input_results_zero: assert property (
        @(posedge CLK) (data_in == 16'b0) |-> (data_out == 16'b0)
    );

endmodule