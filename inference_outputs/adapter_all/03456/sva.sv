module shift_register_4bit_sva (
    input logic clk,
    input logic load,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic ser_out
);

    // Load captures the input into the register on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (out == $past(in))
    );

    // When not loading, the register rotates left by one bit.
    check_rotate_when_not_loading: assert property (
        @(posedge clk) !load |=> (out == {$past(out[2:0]), $past(out[3])})
    );

    // The serial output reflects the previous register MSB.
    check_serial_output_tracks_msb: assert property (
        @(posedge clk) 1'b1 |=> (ser_out == $past(out[3]))
    );

    // Loading also updates the serial output to the previous input MSB.
    check_load_updates_serial_output: assert property (
        @(posedge clk) load |=> (ser_out == $past(in[3]))
    );

    // A rotate operation preserves the serial output value.
    check_rotate_preserves_serial_output: assert property (
        @(posedge clk) !load |=> (ser_out == $past(ser_out))
    );

endmodule