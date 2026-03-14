module prng_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] seed,
    input logic [7:0] q,
    input logic [99:0] shift_reg,
    input logic mux_sel
);

    // In reset, internal state is cleared.
    check_reset_state_regs: assert property (
        @(posedge clk) reset |-> (shift_reg == 100'b0) && (mux_sel == 1'b0)
    );

    // In reset, q equals seed.
    check_reset_q_eq_seed: assert property (
        @(posedge clk) reset |-> (q == seed)
    );

    // On reset deassertion, state remains zero due to prior reset values.
    check_reset_fall_regs_zero: assert property (
        @(posedge clk) $fell(reset) |-> (shift_reg == 100'b0) && (mux_sel == 1'b0)
    );

    // On reset deassertion, q is zero from zeroed taps.
    check_reset_fall_q_zero: assert property (
        @(posedge clk) $fell(reset) |-> (q == 8'h00)
    );

    // When running, shift_reg shifts and inserts previous mux_sel at bit 0.
    check_shift_reg_update: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) === 1'b0) |-> (shift_reg == { $past(shift_reg)[98:0], $past(mux_sel) })
    );

    // When running, mux_sel is XOR of previous shift_reg taps [93,91,87,84].
    check_mux_sel_update: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) === 1'b0) |-> (mux_sel == ($past(shift_reg)[93] ^ $past(shift_reg)[91] ^ $past(shift_reg)[87] ^ $past(shift_reg)[84]))
    );

    // When running, q is formed from previous shift_reg taps.
    check_q_update_from_taps: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) === 1'b0) |-> (q == { $past(shift_reg)[99], $past(shift_reg)[95], $past(shift_reg)[91], $past(shift_reg)[87], $past(shift_reg)[83], $past(shift_reg)[79], $past(shift_reg)[75], $past(shift_reg)[71] })
    );

    // Zero state is absorbing in run mode (remains zero and outputs zero).
    check_zero_state_absorbing: assert property (
        @(posedge clk) disable iff (reset)
            (($past(reset) === 1'b0) && ($past(shift_reg) == 100'b0) && ($past(mux_sel) == 1'b0))
            |-> (shift_reg == 100'b0) && (mux_sel == 1'b0) && (q == 8'h00)
    );

    // While reset is held, state remains stably zero.
    check_reset_state_stable: assert property (
        @(posedge clk) (reset && ($past(reset) === 1'b1)) |-> $stable(shift_reg) && $stable(mux_sel)
    );

endmodule