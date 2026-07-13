module d_ff_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic d,
    input logic q
);

    // Active-low reset drives q low when reset is observed asserted.
    check_reset_forces_q_low: assert property (
        @(posedge clk) disable iff ($initstate) !rst |-> (q == 1'b0)
    );

    // A sampled falling reset leaves q low on that first observed low-reset cycle.
    check_reset_fall_drives_q_low: assert property (
        @(posedge clk) disable iff ($initstate) $fell(rst) |-> (q == 1'b0)
    );

    // Reset dominates a high data input.
    check_reset_dominates_data_high: assert property (
        @(posedge clk) disable iff ($initstate) (!rst && d) |-> (q == 1'b0)
    );

    // Keeping reset low across cycles keeps q stable at zero.
    check_reset_hold_keeps_q_stable: assert property (
        @(posedge clk) disable iff ($initstate) (!rst && $past(!rst)) |-> ($stable(q) && (q == 1'b0))
    );

    // q can only be high when reset is deasserted.
    check_q_high_only_outside_reset: assert property (
        @(posedge clk) disable iff ($initstate) q |-> rst
    );

endmodule