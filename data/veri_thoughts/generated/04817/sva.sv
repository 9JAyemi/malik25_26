module shift_register_32bit_assertions (
    input logic        SHIFT,
    input logic        DATA_IN,
    input logic        SHIFT_OUT,
    input logic [31:0] DATA_OUT
);

    // DATA_OUT[31:1] shifts from the previous DATA_OUT[30:0] after the 3-stage latency.
    check_data_out_shift_upper: assert property (
        @(posedge SHIFT)
        $past(!$initstate, 2) |-> DATA_OUT[31:1] == $past(DATA_OUT[30:0])
    );

    // DATA_OUT[0] reflects DATA_IN from three SHIFT edges earlier.
    check_data_out_lsb_latency: assert property (
        @(posedge SHIFT)
        $past(!$initstate, 2) |-> DATA_OUT[0] == $past(DATA_IN, 3)
    );

    // DATA_OUT[31] matches SHIFT_OUT from two SHIFT edges earlier.
    check_data_out_msb_from_shift_out: assert property (
        @(posedge SHIFT)
        $past(!$initstate) |-> DATA_OUT[31] == $past(SHIFT_OUT, 2)
    );

    // DATA_OUT[30] matches SHIFT_OUT from the previous SHIFT edge.
    check_data_out_bit30_from_shift_out: assert property (
        @(posedge SHIFT)
        $past(!$initstate) |-> DATA_OUT[30] == $past(SHIFT_OUT)
    );

    // SHIFT_OUT is DATA_IN delayed by 32 SHIFT edges through pipeline[0].
    check_shift_out_input_latency: assert property (
        @(posedge SHIFT)
        $past(!$initstate, 31) |-> SHIFT_OUT == $past(DATA_IN, 32)
    );

endmodule