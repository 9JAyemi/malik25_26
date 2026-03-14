module pulse_generator_sva (
    input logic clk,
    input logic ena,
    input logic pulse,
    input logic cycle,
    input logic [1:0] state
);
    ///// Sequential behavior derived from RTL ///// 

    // pulse captures ena from the previous cycle.
    check_pulse_follows_prev_ena: assert property (
        @(posedge clk) $past(1'b1) |-> (pulse == $past(ena))
    );

    // state encodes previous-cycle ena as 2'b01 when ena=1 and 2'b10 when ena=0.
    check_state_encodes_prev_ena: assert property (
        @(posedge clk) $past(1'b1) |-> (state == ($past(ena) ? 2'b01 : 2'b10))
    );

    // cycle captures state[0] from two cycles earlier (due to read-before-write of state).
    check_cycle_follows_prevprev_state_bit0: assert property (
        @(posedge clk) $past(1'b1, 2) |-> (cycle == $past(state[0], 2))
    );

    // cycle equals ena from two cycles earlier.
    check_cycle_follows_prevprev_ena: assert property (
        @(posedge clk) $past(1'b1, 2) |-> (cycle == $past(ena, 2))
    );

    // pulse equals state[0] in the same sampled cycle.
    check_pulse_equals_state_lsb: assert property (
        @(posedge clk) $past(1'b1) |-> (pulse == state[0])
    );

    // state is always one-hot (01 or 10) after first update.
    check_state_onehot: assert property (
        @(posedge clk) $past(1'b1) |-> ((state == 2'b01) || (state == 2'b10))
    );

    // state bits are complementary after first update.
    check_state_bits_complementary: assert property (
        @(posedge clk) $past(1'b1) |-> (state[1] == ~state[0])
    );

    // When previous ena was 1, pulse must be 1.
    check_pulse_assert_when_prev_ena_high: assert property (
        @(posedge clk) ($past(1'b1) && $past(ena)) |-> (pulse == 1'b1)
    );

    // When previous ena was 0, pulse must be 0.
    check_pulse_deassert_when_prev_ena_low: assert property (
        @(posedge clk) ($past(1'b1) && !$past(ena)) |-> (pulse == 1'b0)
    );

    // After first update, state LSB reflects previous ena directly.
    check_state_lsb_matches_prev_ena: assert property (
        @(posedge clk) $past(1'b1) |-> (state[0] == $past(ena))
    );

endmodule