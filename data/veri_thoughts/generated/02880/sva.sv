module delayed_and_sva (
    input  logic        clk,
    input  logic        reset,      // synchronous active-high reset
    input  logic        in,
    input  logic [3:0]  delay,
    input  logic [3:0]  q,
    // Internal signals from RTL
    input  logic [3:0]  shift_reg,
    input  logic [3:0]  counter
);
    // q equals bitwise AND of shift_reg and counter
    check_q_definition: assert property (
        @(posedge clk) disable iff (reset) q == (shift_reg & counter)
    );

    // q is masked by counter (no bit of q can be 1 if corresponding counter bit is 0)
    check_q_masked_by_counter: assert property (
        @(posedge clk) disable iff (reset) (q & ~counter) == 4'b0000
    );

    // q is masked by shift_reg (no bit of q can be 1 if corresponding shift_reg bit is 0)
    check_q_masked_by_shift: assert property (
        @(posedge clk) disable iff (reset) (q & ~shift_reg) == 4'b0000
    );

    // shift_reg[0] captures input from previous cycle when not in reset
    check_shift0_captures_in: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (shift_reg[0] == $past(in))
    );

    // shift_reg[1] captures previous shift_reg[0] when not in reset
    check_shift1_from_shift0: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (shift_reg[1] == $past(shift_reg[0]))
    );

    // shift_reg[2] captures previous shift_reg[1] when not in reset
    check_shift2_from_shift1: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (shift_reg[2] == $past(shift_reg[1]))
    );

    // shift_reg[3] captures previous shift_reg[2] when not in reset
    check_shift3_from_shift2: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (shift_reg[3] == $past(shift_reg[2]))
    );

    // counter resets to 0 on next cycle when previous counter equaled current delay
    check_counter_resets_on_match: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && ($past(counter) == delay) |-> (counter == 4'b0000)
    );

    // counter increments by 1 on next cycle when previous counter did not equal current delay
    check_counter_increments_on_no_match: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && ($past(counter) != delay) |-> (counter == ($past(counter) + 1))
    );

    // When reset is asserted, on the next cycle the registers (and hence q) are cleared
    reset_clears_next_cycle: assert property (
        @(posedge clk) reset |-> ##1 ((shift_reg == 4'b0000) && (counter == 4'b0000) && (q == 4'b0000))
    );

endmodule