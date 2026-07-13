module shift_module_sva (
    input logic clk,
    input logic [7:0] input_num,
    input logic control_signal,
    input logic [7:0] shifted_num
);

    // High control selects a left shift by one.
    check_left_shift_value: assert property (
        @(posedge clk) (control_signal == 1'b1) |-> (shifted_num == (input_num << 1))
    );

    // Low control selects a right shift by one.
    check_right_shift_value: assert property (
        @(posedge clk) (control_signal == 1'b0) |-> (shifted_num == (input_num >> 1))
    );

    // Left shift drives a zero into bit 0.
    check_left_shift_lsb_zero: assert property (
        @(posedge clk) (control_signal == 1'b1) |-> (shifted_num[0] == 1'b0)
    );

    // Right shift drives a zero into bit 7.
    check_right_shift_msb_zero: assert property (
        @(posedge clk) (control_signal == 1'b0) |-> (shifted_num[7] == 1'b0)
    );

    // Left shift maps input bits [6:0] to output bits [7:1].
    check_left_shift_bit_map: assert property (
        @(posedge clk) (control_signal == 1'b1) |-> (shifted_num[7:1] == input_num[6:0])
    );

    // Right shift maps input bits [7:1] to output bits [6:0].
    check_right_shift_bit_map: assert property (
        @(posedge clk) (control_signal == 1'b0) |-> (shifted_num[6:0] == input_num[7:1])
    );

endmodule