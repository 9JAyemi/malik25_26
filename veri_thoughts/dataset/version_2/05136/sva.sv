module barrel_shifter_8bit_sva(
    input logic [7:0] data_in,
    input logic [2:0] shift_amount,
    input logic [7:0] data_out
);

    // Shift amount 0 passes the input through.
    check_shift_amt_0: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd0) |-> (data_out == data_in)
    );

    // Shift amount 1 shifts left by one and inserts a zero LSB.
    check_shift_amt_1: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd1) |-> (data_out == {data_in[6:0], 1'b0})
    );

    // Shift amount 2 shifts left by two and inserts two zero LSBs.
    check_shift_amt_2: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd2) |-> (data_out == {data_in[5:0], 2'b00})
    );

    // Shift amount 3 shifts left by three and inserts three zero LSBs.
    check_shift_amt_3: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd3) |-> (data_out == {data_in[4:0], 3'b000})
    );

    // Shift amount 4 shifts left by four and inserts four zero LSBs.
    check_shift_amt_4: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd4) |-> (data_out == {data_in[3:0], 4'b0000})
    );

    // Shift amount 5 shifts left by five and inserts five zero LSBs.
    check_shift_amt_5: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd5) |-> (data_out == {data_in[2:0], 5'b00000})
    );

    // Shift amount 6 shifts left by six and inserts six zero LSBs.
    check_shift_amt_6: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd6) |-> (data_out == {data_in[1:0], 6'b000000})
    );

    // Shift amount 7 leaves only bit 0 in the MSB position.
    check_shift_amt_7: assert property (
        @($global_clock) disable iff (1'b0)
        (shift_amount == 3'd7) |-> (data_out == {data_in[0], 7'b0000000})
    );

    // A zero input always produces a zero output.
    check_zero_input_zero_output: assert property (
        @($global_clock) disable iff (1'b0)
        (data_in == 8'h00) |-> (data_out == 8'h00)
    );

endmodule