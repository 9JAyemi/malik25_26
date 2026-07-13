module shift_register_4bit_sva (
    input logic clk,
    input logic load,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic ser_out
);

    // Load captures the input vector into the register on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (out == $past(in))
    );

    // When not loading, the register rotates left by one bit.
    check_shift_rotates_register: assert property (
        @(posedge clk) !load |=> (out == { $past(out[2:0]), $past(out[3]) })
    );

    // The serial output is the previous cycle's MSB.
    check_serial_output_tracks_msb: assert property (
        @(posedge clk) 1'b1 |=> (ser_out == $past(out[3]))
    );

    // Loading also drives the serial output high on the next cycle.
    check_load_sets_serial_output: assert property (
        @(posedge clk) load |=> (ser_out == 1'b1)
    );

    // A left rotation with zero in bit 3 clears the serial output.
    check_shift_clears_serial_output: assert property (
        @(posedge clk) (!load && (in[3] == 1'b0)) |=> (ser_out == 1'b0)
    );

endmodule