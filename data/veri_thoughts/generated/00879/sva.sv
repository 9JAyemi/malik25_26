module shift_reg_sva (
    input logic d,
    input logic clk,
    input logic en,
    input logic [7:0] q
);
    // Analysis: Clock is clk (posedge). No reset present. Mixed logic: sequential shift_reg update on clk, q combinationally mirrors shift_reg. Behavior: on en, q shifts left with d loaded into q[0]; otherwise q holds.

    ///// Shift/hold behavior /////

    // When disabled, q holds its value across the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge clk) (!en) |=> (q == $past(q))
    );

    // When enabled, LSB captures d from the previous cycle.
    check_lsb_captures_d_when_enabled: assert property (
        @(posedge clk) (en) |=> (q[0] == $past(d))
    );

    // When enabled, bit[1] takes previous bit[0].
    check_shift_bit1: assert property (
        @(posedge clk) (en) |=> (q[1] == $past(q[0]))
    );

    // When enabled, bit[2] takes previous bit[1].
    check_shift_bit2: assert property (
        @(posedge clk) (en) |=> (q[2] == $past(q[1]))
    );

    // When enabled, bit[3] takes previous bit[2].
    check_shift_bit3: assert property (
        @(posedge clk) (en) |=> (q[3] == $past(q[2]))
    );

    // When enabled, bit[4] takes previous bit[3].
    check_shift_bit4: assert property (
        @(posedge clk) (en) |=> (q[4] == $past(q[3]))
    );

    // When enabled, bit[5] takes previous bit[4].
    check_shift_bit5: assert property (
        @(posedge clk) (en) |=> (q[5] == $past(q[4]))
    );

    // When enabled, bit[6] takes previous bit[5].
    check_shift_bit6: assert property (
        @(posedge clk) (en) |=> (q[6] == $past(q[5]))
    );

    // When enabled, bit[7] takes previous bit[6].
    check_shift_bit7: assert property (
        @(posedge clk) (en) |=> (q[7] == $past(q[6]))
    );

    // When enabled, the whole word shifts left with d appended (redundant but comprehensive).
    check_full_word_shift_when_enabled: assert property (
        @(posedge clk) (en) |=> (q == { $past(q[6:0]), $past(d) })
    );

endmodule