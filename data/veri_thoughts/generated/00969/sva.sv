module up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic reset,
    input logic [3:0] q
);
    // On a clock where reset=1, q must be 0 on the next clock.
    check_reset_to_zero_next: assert property (
        @(posedge clk) reset |=> (q == 4'd0)
    );

    // While reset is held high across clocks, q stays 0.
    check_reset_held_forces_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'd0)
    );

    // General 1-cycle update: after any active cycle, q matches the prior cycle's rule.
    check_general_state_update: assert property (
        @(posedge clk) disable iff (reset)
            $past(1'b1) |-> ( q == ( $past(reset) ? 4'd0
                                              : ($past(up_down) ? ($past(q) + 4'd1)
                                                                : ($past(q) - 4'd1)) ) )
    );

    // If last cycle was active and up_down=1, q increments by 1 modulo 16.
    check_increment_step: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(up_down)) |-> (q == ($past(q) + 4'd1))
    );

    // If last cycle was active and up_down=0, q decrements by 1 modulo 16.
    check_decrement_step: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && !$past(up_down)) |-> (q == ($past(q) - 4'd1))
    );

    // Increment wrap: from 0xF with up_down=1 goes to 0x0.
    check_wrap_inc_from_max: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(up_down) && ($past(q) == 4'hF)) |-> (q == 4'h0)
    );

    // Decrement wrap: from 0x0 with up_down=0 goes to 0xF.
    check_wrap_dec_from_min: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && !$past(up_down) && ($past(q) == 4'h0)) |-> (q == 4'hF)
    );

    // On every active cycle, q must change value (never hold).
    check_value_changes_each_active_cycle: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (q != $past(q))
    );

    // Two consecutive active increments advance q by 2 modulo 16.
    check_two_cycle_inc_progress: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset && up_down, 2) && $past(!reset && up_down, 1))
                |-> (q == ($past(q, 2) + 4'd2))
    );

    // Two consecutive active decrements decrease q by 2 modulo 16.
    check_two_cycle_dec_progress: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset && !up_down, 2) && $past(!reset && !up_down, 1))
                |-> (q == ($past(q, 2) - 4'd2))
    );

    // On the cycle immediately after reset was 1, q must be 0 (release behavior).
    check_reset_release_yields_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) && !reset) |-> (q == 4'd0)
    );
endmodule