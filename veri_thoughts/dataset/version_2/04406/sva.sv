module ring_delay_sva (
    input logic clk,
    input logic d,
    input logic [3:0] delay,
    input logic q,
    input logic [2:0] shift_reg,
    input logic [3:0] delay_counter
);

    // shift_reg[0] captures d every cycle.
    check_shift_reg_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[0] == $past(d))
    );

    // shift_reg[1] takes the previous shift_reg[0].
    check_shift_reg_stage1: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[1] == $past(shift_reg[0]))
    );

    // shift_reg[2] takes the previous shift_reg[1].
    check_shift_reg_stage2: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg[2] == $past(shift_reg[1]))
    );

    // delay_counter resets when it matches delay.
    check_counter_resets_on_match: assert property (
        @(posedge clk) (delay_counter == delay) |=> (delay_counter == 4'd0)
    );

    // delay_counter increments when it does not match delay.
    check_counter_increments_on_mismatch: assert property (
        @(posedge clk) (delay_counter != delay) |=> (delay_counter == ($past(delay_counter) + 4'd1))
    );

    // q updates from the previous shift_reg[2] on a match.
    check_q_updates_on_match: assert property (
        @(posedge clk) (delay_counter == delay) |=> (q == $past(shift_reg[2]))
    );

    // q holds its value when no delayed output is taken.
    check_q_holds_on_mismatch: assert property (
        @(posedge clk) (delay_counter != delay) |=> (q == $past(q))
    );

endmodule