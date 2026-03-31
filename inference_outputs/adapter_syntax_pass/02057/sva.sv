module shift_register_sva (
    input logic in,
    input logic shift,
    input logic out,
    input logic [7:0] register
);

    // Register bit 0 captures the input on each shift edge.
    check_register_bit0_captures_input: assert property (
        @(posedge shift) 1'b1 |=> (register[0] == $past(in))
    );

    // Register bits 1 through 7 shift from bit 2 through bit 8.
    check_register_shifts_upper_bits: assert property (
        @(posedge shift) 1'b1 |=> (register[7:1] == $past(register[6:0]))
    );

    // The output is always the MSB of the register.
    check_out_matches_register_msb: assert property (
        @(posedge shift) out == register[7]
    );

    // The output reflects the input captured into bit 0.
    check_out_matches_input_capture: assert property (
        @(posedge shift) 1'b1 |=> (out == $past(in))
    );

endmodule