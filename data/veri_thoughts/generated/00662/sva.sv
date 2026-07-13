module sync_up_counter_sva #(
    parameter WIDTH = 4
) (
    input logic                 clk,
    input logic                 rst,
    input logic                 load,
    input logic [WIDTH-1:0]     data_in,
    input logic [WIDTH-1:0]     count
);
    // After reset deassertion, count holds zero (from prior reset cycle).
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == '0)
    );

    // When load is asserted (no reset), next count equals data_in sampled this cycle.
    check_load_updates_next: assert property (
        @(posedge clk) disable iff (rst) load |=> (count == $past(data_in))
    );

    // When not loading (no reset), next count increments by one modulo WIDTH.
    check_increment_on_no_load: assert property (
        @(posedge clk) disable iff (rst) !load |=> (count == $past(count) + 1'b1)
    );

    // With two consecutive cycles of no load and no reset, count advances by two.
    check_two_cycle_increment_no_load: assert property (
        @(posedge clk) disable iff (rst) (!rst && !load) ##1 (!rst && !load) |=> (count == $past(count,2) + 2)
    );

    // With back-to-back loads (no reset), the second load value is observed next.
    check_double_load_last_wins: assert property (
        @(posedge clk) disable iff (rst) (load && !rst) ##1 (load && !rst) |=> (count == $past(data_in))
    );

    // Load then no-load (no reset): after two cycles, count equals loaded value + 1.
    check_load_then_increment_result: assert property (
        @(posedge clk) disable iff (rst) (load && !rst) ##1 (!rst && !load) |=> (count == $past(data_in,2) + 1'b1)
    );

    // No-load then load (no reset): after two cycles, count equals the load value.
    check_increment_then_load_result: assert property (
        @(posedge clk) disable iff (rst) (!rst && !load) ##1 (load && !rst) |=> (count == $past(data_in))
    );

    // When count is max and no load (no reset), next count wraps to zero.
    check_wraparound_when_max: assert property (
        @(posedge clk) disable iff (rst) (!load && (count == {WIDTH{1'b1}})) |=> (count == '0)
    );

    // Immediately after reset release with no load, the first update increments from zero.
    check_post_reset_first_no_load_increments: assert property (
        @(posedge clk) disable iff (rst) ($fell(rst) && !load) |=> (count == $past(count) + 1'b1)
    );

    // General next-state: if previous cycle was not in reset, implement load/++ function.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (count == ($past(load) ? $past(data_in) : ($past(count) + 1'b1)))
    );
endmodule