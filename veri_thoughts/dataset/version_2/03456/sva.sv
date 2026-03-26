module shift_register_4bit_assertions (
    input logic       clk,
    input logic       load,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic       ser_out
);

    // Load copies the input into the register.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> out == $past(in)
    );

    // Without load, the register rotates left with wraparound.
    check_shift_rotates_register: assert property (
        @(posedge clk) !load |=> out == {$past(out[2:0]), $past(out[3])}
    );

    // On a shift cycle, the previous MSB wraps into bit 0.
    check_shift_wraps_msb_to_lsb: assert property (
        @(posedge clk) !load |=> out[0] == $past(out[3])
    );

    // On a shift cycle, bits [3:1] come from the previous [2:0].
    check_shift_moves_lower_bits_up: assert property (
        @(posedge clk) !load |=> out[3:1] == $past(out[2:0])
    );

    // The serial output is always the previous cycle's MSB.
    check_ser_out_tracks_previous_msb: assert property (
        @(posedge clk) 1'b1 |=> ser_out == $past(out[3])
    );

    // On a shift cycle, serial output matches the wrapped bit on out[0].
    check_shift_ser_out_matches_lsb: assert property (
        @(posedge clk) !load |=> ser_out == out[0]
    );

endmodule