module shift_register_sva(
    input logic        CLK,
    input logic        LOAD,
    input logic        SER_IN,
    input logic [31:0] PAR_IN,
    input logic        SER_OUT
);

    // A load makes the next sampled serial output equal to the loaded MSB.
    check_load_updates_msb: assert property (
        @(posedge CLK) LOAD |=> (SER_OUT == $past(PAR_IN[31]))
    );

    // One shift after a load exposes PAR_IN[30] on the serial output.
    check_first_shift_exposes_bit30: assert property (
        @(posedge CLK) (LOAD ##1 !LOAD) |=> (SER_OUT == $past(PAR_IN[30], 2))
    );

    // Two shifts after a load expose PAR_IN[29] on the serial output.
    check_second_shift_exposes_bit29: assert property (
        @(posedge CLK) (LOAD ##1 !LOAD ##1 !LOAD) |=> (SER_OUT == $past(PAR_IN[29], 3))
    );

    // Thirty-one shifts after a load expose PAR_IN[0] on the serial output.
    check_thirty_one_shifts_expose_bit0: assert property (
        @(posedge CLK) (LOAD ##1 (!LOAD[*31])) |=> (SER_OUT == $past(PAR_IN[0], 32))
    );

    // Thirty-two shifts after a load expose the first shifted-in serial bit.
    check_thirty_two_shifts_expose_first_serial_in: assert property (
        @(posedge CLK) (LOAD ##1 (!LOAD[*32])) |=> (SER_OUT == $past(SER_IN, 32))
    );

endmodule