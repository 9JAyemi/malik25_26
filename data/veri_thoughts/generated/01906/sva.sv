module counter_mod_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] out
);

    // During reset, next-cycle output must be zero.
    reset_clears_next: assert property (
        @(posedge clk) (!rst) |=> (out == 4'b0000)
    );

    // If reset is held across consecutive cycles, output is zero now.
    reset_held_keeps_zero: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (out == 4'b0000)
    );

    // When not in reset in consecutive cycles, output increments by one.
    run_increments_by_one: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (out == $past(out) + 4'd1)
    );

    // Wrap from 0xF to 0x0 when running.
    wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

    // LSB toggles every running cycle.
    lsb_toggles_when_running: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (out[0] == ~$past(out[0]))
    );

    // Output changes every running cycle (no hold).
    out_changes_each_running_cycle: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (out != $past(out))
    );

    // On reset release, next-cycle output becomes 1.
    release_next_is_one: assert property (
        @(posedge clk) $rose(rst) |=> (out == 4'd1)
    );

    // While reset is held, output remains stable (stays at zero).
    reset_keeps_out_stable: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (out == $past(out))
    );

    // When running, seeing 0 implies previous was 0xF (wrap property).
    zero_implies_prev_f_when_running: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && (out == 4'd0)) |-> ($past(out) == 4'hF)
    );

endmodule