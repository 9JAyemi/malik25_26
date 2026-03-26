module shift_comp_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] serial_in,
    input logic        shift_direction,
    input logic [15:0] serial_out,
    input logic        final_output
);

    // Reset clears the shift register output on the following clock.
    check_reset_clears_serial_out: assert property (
        @(posedge clk) reset |=> (serial_out == 16'b0)
    );

    // Reset drives the comparator-based output low on the following clock.
    check_reset_clears_final_output: assert property (
        @(posedge clk) reset |=> (final_output == 1'b0)
    );

    // shift_direction high shifts toward MSB and loads serial_in[0] into bit 0.
    check_shift_left_update: assert property (
        @(posedge clk) disable iff (reset)
        shift_direction |=> (serial_out == { $past(serial_out[14:0]), $past(serial_in[0]) })
    );

    // shift_direction low shifts toward LSB and loads serial_in[15] into bit 15.
    check_shift_right_update: assert property (
        @(posedge clk) disable iff (reset)
        !shift_direction |=> (serial_out == { $past(serial_in[15]), $past(serial_out[15:1]) })
    );

    // A low nibble equal to 4'b1010 makes final_output high.
    check_final_output_equal_case: assert property (
        @(posedge clk) disable iff (reset)
        (serial_out[3:0] == 4'b1010) |-> (final_output == 1'b1)
    );

    // A low nibble greater than 4'b1010 makes final_output high.
    check_final_output_greater_case: assert property (
        @(posedge clk) disable iff (reset)
        (serial_out[3:0] > 4'b1010) |-> (final_output == 1'b1)
    );

    // A low nibble less than 4'b1010 makes final_output low.
    check_final_output_less_case: assert property (
        @(posedge clk) disable iff (reset)
        (serial_out[3:0] < 4'b1010) |-> (final_output == 1'b0)
    );

endmodule