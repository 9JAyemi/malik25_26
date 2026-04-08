module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic       serial_in,
    input logic [2:0] out
);

    // Load writes the zero-extended serial input on the next clock.
    check_load_writes_zero_extended_serial: assert property (
        @(posedge clk) disable iff ($initstate)
        load |=> (out == {2'b00, $past(serial_in)})
    );

    // Load clears the upper two bits on the next clock.
    check_load_clears_upper_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        load |=> (out[2:1] == 2'b00)
    );

    // Shift mode moves prior out[1:0] up and brings in serial_in.
    check_shift_writes_shifted_value: assert property (
        @(posedge clk) disable iff ($initstate)
        !load |=> (out == {$past(out[1:0]), $past(serial_in)})
    );

    // Shift mode copies the previous low bits into the upper positions.
    check_shift_moves_previous_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        !load |=> (out[2:1] == $past(out[1:0]))
    );

    // Shift mode captures the serial input into the LSB.
    check_shift_captures_serial_in_lsb: assert property (
        @(posedge clk) disable iff ($initstate)
        !load |=> (out[0] == $past(serial_in))
    );

endmodule