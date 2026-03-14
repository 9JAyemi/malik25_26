module barrel_shifter_sva (
    input logic [31:0] data,
    input logic [4:0] shift_amount,
    input logic shift_direction,
    input logic [31:0] shifted_data
);
    // Sample on any edge of inputs (no clock/reset in RTL)
    default clocking cb @(
        posedge shift_direction or negedge shift_direction
        or posedge data[0] or negedge data[0]
        or posedge data[1] or negedge data[1]
        or posedge data[2] or negedge data[2]
        or posedge data[3] or negedge data[3]
        or posedge data[4] or negedge data[4]
        or posedge data[5] or negedge data[5]
        or posedge data[6] or negedge data[6]
        or posedge data[7] or negedge data[7]
        or posedge data[8] or negedge data[8]
        or posedge data[9] or negedge data[9]
        or posedge data[10] or negedge data[10]
        or posedge data[11] or negedge data[11]
        or posedge data[12] or negedge data[12]
        or posedge data[13] or negedge data[13]
        or posedge data[14] or negedge data[14]
        or posedge data[15] or negedge data[15]
        or posedge data[16] or negedge data[16]
        or posedge data[17] or negedge data[17]
        or posedge data[18] or negedge data[18]
        or posedge data[19] or negedge data[19]
        or posedge data[20] or negedge data[20]
        or posedge data[21] or negedge data[21]
        or posedge data[22] or negedge data[22]
        or posedge data[23] or negedge data[23]
        or posedge data[24] or negedge data[24]
        or posedge data[25] or negedge data[25]
        or posedge data[26] or negedge data[26]
        or posedge data[27] or negedge data[27]
        or posedge data[28] or negedge data[28]
        or posedge data[29] or negedge data[29]
        or posedge data[30] or negedge data[30]
        or posedge data[31] or negedge data[31]
        or posedge shift_amount[0] or negedge shift_amount[0]
        or posedge shift_amount[1] or negedge shift_amount[1]
        or posedge shift_amount[2] or negedge shift_amount[2]
        or posedge shift_amount[3] or negedge shift_amount[3]
        or posedge shift_amount[4] or negedge shift_amount[4]
    ); endclocking

    // Output matches left shift when shift_direction is 1.
    check_left_function: assert property (
        shift_direction |-> (shifted_data == (data << shift_amount))
    );

    // Output matches right shift when shift_direction is 0.
    check_right_function: assert property (
        !shift_direction |-> (shifted_data == (data >> shift_amount))
    );

    // Shift by zero passes data through regardless of direction.
    check_shift_by_zero_passthrough: assert property (
        (shift_amount == 5'd0) |-> (shifted_data == data)
    );

    // Zero input always yields zero output.
    check_zero_input_zero_output: assert property (
        (data == 32'd0) |-> (shifted_data == 32'd0)
    );

    // Left shift zero-fills lower bits when amount != 0.
    check_left_zero_fill_lsb: assert property (
        (shift_direction && (shift_amount != 5'd0)) |-> (shifted_data[shift_amount-1:0] == '0)
    );

    // Right shift zero-fills upper bits when amount != 0.
    check_right_zero_fill_msb: assert property (
        (!shift_direction && (shift_amount != 5'd0)) |-> (shifted_data[31 -: shift_amount] == '0)
    );

    // Left shift by 31 moves bit 0 to bit 31 and clears others.
    check_left_shift_by_31: assert property (
        (shift_direction && (shift_amount == 5'd31)) |-> (shifted_data[31] == data[0]) && (shifted_data[30:0] == 31'd0)
    );

    // Right shift by 31 moves bit 31 to bit 0 and clears others.
    check_right_shift_by_31: assert property (
        (!shift_direction && (shift_amount == 5'd31)) |-> (shifted_data[0] == data[31]) && (shifted_data[31:1] == 31'd0)
    );

    // Left shift by 1 maps bits up by one and clears LSB.
    check_left_shift_by_1: assert property (
        (shift_direction && (shift_amount == 5'd1)) |-> (shifted_data[31:1] == data[30:0]) && (shifted_data[0] == 1'b0)
    );

    // Right shift by 1 maps bits down by one and clears MSB.
    check_right_shift_by_1: assert property (
        (!shift_direction && (shift_amount == 5'd1)) |-> (shifted_data[30:0] == data[31:1]) && (shifted_data[31] == 1'b0)
    );

endmodule