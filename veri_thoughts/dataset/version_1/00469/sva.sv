module johnson_counter_sva (
    input logic       clk,
    input logic [3:0] Q,
    input logic [3:0] shift_reg
);

    // shift_reg rotates by one bit on every clock.
    check_shift_reg_rotation: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg)) |-> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])}
    );

    // Q[0] is the XOR of the prior shift_reg[0] and shift_reg[3].
    check_q_lsb_from_prior_shift: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg)) |-> Q[0] == ($past(shift_reg[0]) ^ $past(shift_reg[3]))
    );

    // The upper bits of Q are always zero after Q is first updated.
    check_q_upper_bits_zero: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg)) |-> Q[3:1] == 3'b000
    );

    // The current Q[0] matches the current rotated shift_reg bits.
    check_q_lsb_matches_current_shift: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg)) |-> Q[0] == (shift_reg[1] ^ shift_reg[0])
    );

    // A 4-bit rotation returns shift_reg to the same value after four clocks.
    check_shift_reg_period_four: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg, 4)) |-> shift_reg == $past(shift_reg, 4)
    );

    // Q repeats every four clocks once four updated Q values exist.
    check_q_period_four: assert property (
        @(posedge clk)
        !$isunknown($past(shift_reg, 5)) |-> Q == $past(Q, 4)
    );

endmodule