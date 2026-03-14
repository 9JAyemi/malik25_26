module shift_register_sva (
    input logic CLK,
    input logic LOAD,
    input logic SHIFT,
    input logic [3:0] D,
    input logic [3:0] Q
);
    // On LOAD, next Q captures D (LOAD has priority over SHIFT).
    check_load_captures_d: assert property (
        @(posedge CLK) LOAD |=> (Q == $past(D))
    );

    // On SHIFT without LOAD, next Q is left-shifted with zero fill.
    check_shift_left_with_zero_fill: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q == { $past(Q)[2:0], 1'b0 })
    );

    // With neither LOAD nor SHIFT, Q holds its value.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!LOAD && !SHIFT) |=> (Q == $past(Q))
    );

    // If both LOAD and SHIFT are asserted, LOAD wins and Q captures D.
    check_load_priority_over_shift: assert property (
        @(posedge CLK) (LOAD && SHIFT) |=> (Q == $past(D))
    );

    // On SHIFT without LOAD, LSB becomes 0 next cycle.
    check_shift_zero_fills_lsb: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[0] == 1'b0)
    );

    // On SHIFT without LOAD, Q[3] comes from previous Q[2].
    check_shift_bit3_from_bit2: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[3] == $past(Q[2]))
    );

    // On SHIFT without LOAD, Q[2] comes from previous Q[1].
    check_shift_bit2_from_bit1: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[2] == $past(Q[1]))
    );

    // On SHIFT without LOAD, Q[1] comes from previous Q[0].
    check_shift_bit1_from_bit0: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[1] == $past(Q[0]))
    );

    // Four consecutive SHIFTs without LOAD zero out the register by the next cycle.
    sequence four_consecutive_shifts_no_load;
        (!LOAD && SHIFT)[*4];
    endsequence
    check_four_shifts_zero_out: assert property (
        @(posedge CLK) four_consecutive_shifts_no_load |=> (Q == 4'b0000)
    );

    // If Q is 0 and a SHIFT occurs without LOAD, Q remains 0 next cycle.
    check_zero_stays_zero_under_shift: assert property (
        @(posedge CLK) (!LOAD && SHIFT && (Q == 4'b0000)) |=> (Q == 4'b0000)
    );
endmodule