module program_counter2a_sva (
    input logic clk,
    input logic rst,
    input logic [0:31] next_pc
);
    // When rst is asserted, next_pc is driven to 0 on the same clock.
    check_reset_drives_zero: assert property (
        @(posedge clk) rst |-> (next_pc == 32'd0)
    );

    // If two consecutive cycles are in reset, next_pc stays at 0 and stable.
    check_stable_zero_during_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (next_pc == 32'd0) && (next_pc == $past(next_pc))
    );

    // When running (both current and previous cycles not in reset), next_pc increments by 4.
    check_increment_by_4_when_running: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (next_pc == $past(next_pc) + 32'd4)
    );

    // On reset deassertion edge, next_pc increments by 4 from the prior value.
    check_increment_by_4_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (next_pc == $past(next_pc) + 32'd4)
    );

    // While running, next_pc changes every cycle.
    check_changes_each_cycle_when_running: assert property (
        @(posedge clk) disable iff (rst) (next_pc != $past(next_pc))
    );

    // While running, next_pc is monotonically non-decreasing (unsigned).
    check_monotonic_when_running: assert property (
        @(posedge clk) disable iff (rst) (next_pc >= $past(next_pc))
    );

    // While running, the two LSBs remain 0 (word-aligned).
    check_lsb_alignment_when_running: assert property (
        @(posedge clk) disable iff (rst) (next_pc[31:30] == 2'b00)
    );
endmodule