module shift_register_sva (
    input logic [3:0] data_in,
    input logic       shift,
    input logic [3:0] data_out,
    input logic [3:0] shift_reg
);
    // No clock/reset in RTL; sample assertions on $global_clock.

    // data_out continuously mirrors internal shift_reg.
    check_data_out_mirrors_shift_reg: assert property (
        @($global_clock) data_out == shift_reg
    );

    // When shift is 0, output equals data_in (load path).
    check_load_when_shift_low: assert property (
        @($global_clock) (shift == 1'b0) |-> (data_out == data_in)
    );

    // When shift is 1, next output is left shift of previous output with 0 fill.
    check_shift_left_when_high: assert property (
        @($global_clock) (shift == 1'b1) |=> (data_out == { $past(data_out)[2:0], 1'b0 })
    );

    // When shifting, the new LSB is 0.
    check_shift_lsb_zero: assert property (
        @($global_clock) (shift == 1'b1) |=> (data_out[0] == 1'b0)
    );

    // When shifting, the new MSB equals previous bit2.
    check_shift_msb_from_bit2: assert property (
        @($global_clock) (shift == 1'b1) |=> (data_out[3] == $past(data_out[2]))
    );

    // When shifting, bit2 comes from previous bit1.
    check_shift_bit2_from_bit1: assert property (
        @($global_clock) (shift == 1'b1) |=> (data_out[2] == $past(data_out[1]))
    );

    // When shifting, bit1 comes from previous bit0.
    check_shift_bit1_from_bit0: assert property (
        @($global_clock) (shift == 1'b1) |=> (data_out[1] == $past(data_out[0]))
    );

    // Two consecutive high shifts append two zeros over two cycles.
    check_two_consecutive_shifts: assert property (
        @($global_clock) (shift == 1'b1 && $past(shift) == 1'b1) |=> (data_out == { $past($past(data_out))[1:0], 2'b00 })
    );

    // On falling edge of shift, the load path drives data_out from data_in.
    check_load_on_shift_fall: assert property (
        @($global_clock) $fell(shift) |-> (data_out == data_in)
    );

    // Shifting zero keeps zero.
    check_shift_zero_stays_zero: assert property (
        @($global_clock) (shift == 1'b1 && $past(data_out) == 4'b0000) |=> (data_out == 4'b0000)
    );
endmodule