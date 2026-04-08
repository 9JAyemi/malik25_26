module shift_register_sva (
    input  logic       serial_in,
    input  logic       shift,
    input  logic [3:0] parallel_out
);

    // The register shifts prior contents and loads the prior serial input into bit 0.
    check_full_shift_update: assert property (
        @(posedge shift)
        1'b1 |=> parallel_out == {$past(parallel_out[2:0]), $past(serial_in)}
    );

    // Bit 3 takes the previous value of bit 2.
    check_bit3_shift: assert property (
        @(posedge shift)
        1'b1 |=> parallel_out[3] == $past(parallel_out[2])
    );

    // Bit 2 takes the previous value of bit 1.
    check_bit2_shift: assert property (
        @(posedge shift)
        1'b1 |=> parallel_out[2] == $past(parallel_out[1])
    );

    // Bit 1 takes the previous value of bit 0.
    check_bit1_shift: assert property (
        @(posedge shift)
        1'b1 |=> parallel_out[1] == $past(parallel_out[0])
    );

    // Bit 0 loads the previous serial input.
    check_bit0_load: assert property (
        @(posedge shift)
        1'b1 |=> parallel_out[0] == $past(serial_in)
    );

    // After four shift edges, the register reflects the last four serial inputs.
    check_last_four_serial_inputs: assert property (
        @(posedge shift)
        1'b1 ##1 1'b1 ##1 1'b1 ##1 1'b1 |=> parallel_out == {
            $past(serial_in,4),
            $past(serial_in,3),
            $past(serial_in,2),
            $past(serial_in,1)
        }
    );

endmodule