module counter_sva (
    input logic [7:0] count,
    input logic       clk,
    input logic       reset
);

    // Sampled count is always zero or the previous sampled value plus one.
    check_count_zero_or_increment: assert property (
        @(posedge clk) disable iff ($initstate)
        (count == 8'h00) || (count == ($past(count) + 8'h01))
    );

    // A reset seen on the prior clock forces the sampled count to zero.
    check_prev_reset_drives_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 8'h00)
    );

    // Any nonzero sampled count in active mode must be the incremented prior value.
    check_nonzero_active_counts_increment: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (count != 8'h00) |-> (count == ($past(count) + 8'h01))
    );

    // A sampled 8'hFF always becomes a sampled 8'h00 on the next clock.
    check_ff_wraps_to_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(count) == 8'hFF) |-> (count == 8'h00)
    );

    // From a sampled zero in active mode, the next sample is zero or one.
    check_zero_state_holds_or_advances: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(count) == 8'h00) |-> ((count == 8'h00) || (count == 8'h01))
    );

endmodule