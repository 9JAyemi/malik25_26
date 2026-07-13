module RegisterMultiplexer_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [11:0] D,
    input logic [11:0] Q
);
    // Clk: clk (posedge). Reset: rst (active-high, asynchronous). Sequential register with async reset and load-enable.

    // Reset asserted: Q becomes zero on the next sampled clock edge.
    check_reset_clears_q_next: assert property (
        @(posedge clk) rst |=> (Q == 12'b0)
    );

    // While reset stays asserted across consecutive clocks, Q is zero each sampled cycle.
    check_reset_held_forces_zero_each_cycle: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (Q == 12'b0)
    );

    // If reset and load are both high at a clock edge, Q is zero on the next sampled edge (reset dominates).
    check_reset_dominates_load_next: assert property (
        @(posedge clk) (rst && load) |=> (Q == 12'b0)
    );

    // Immediately after a sampled reset deassertion, Q is still zero at that clock edge.
    check_q_zero_on_reset_fall_sample: assert property (
        @(posedge clk) $fell(rst) |-> (Q == 12'b0)
    );

    // After a sampled reset, if no load occurs on the following clock, Q remains zero.
    check_zero_persists_after_reset_without_load: assert property (
        @(posedge clk) disable iff (rst) ($past(rst) && !load) |-> (Q == 12'b0)
    );

    // On a sampled reset rising edge, Q becomes zero on the next sampled clock edge.
    check_q_zero_on_reset_rise_next: assert property (
        @(posedge clk) $rose(rst) |=> (Q == 12'b0)
    );
endmodule