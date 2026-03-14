module up_counter_sva (
    input logic clk,
    input logic load,
    input logic [3:0] load_value,
    input logic [3:0] count
);
    // If load is high, next-cycle sampled count equals that cycle's load_value.
    check_load_updates_count_next_cycle: assert property (
        @(posedge clk) load |=> (count == $past(load_value))
    );

    // If load is low, next-cycle sampled count equals previous count + 1 (mod 16).
    check_increment_on_no_load: assert property (
        @(posedge clk) !load |=> (count == ($past(count) + 4'd1))
    );

    // Next-cycle sampled count always equals either prior load_value or prior count + 1.
    check_next_count_comes_from_load_or_increment: assert property (
        @(posedge clk) 1'b1 |=> (count == ($past(load) ? $past(load_value) : ($past(count) + 4'd1)))
    );

    // With no load and count at max, next-cycle sampled count wraps to 0.
    check_wrap_from_max_on_increment: assert property (
        @(posedge clk) (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

    // With no load and count at 0, next-cycle sampled count becomes 1.
    check_increment_from_zero: assert property (
        @(posedge clk) (!load && (count == 4'h0)) |=> (count == 4'h1)
    );

    // If load assigns the same value as current count, next-cycle sampled count holds.
    check_stable_when_load_assigns_same: assert property (
        @(posedge clk) (load && (load_value == count)) |=> (count == $past(count))
    );

    // Two consecutive cycles of no load advance count by two.
    check_two_cycle_increment_when_no_load: assert property (
        @(posedge clk) (!load ##1 !load) |=> (count == ($past(count, 2) + 4'd2))
    );

    // Three consecutive cycles of no load advance count by three.
    check_three_cycle_increment_when_no_load: assert property (
        @(posedge clk) (!load ##1 !load ##1 !load) |=> (count == ($past(count, 3) + 4'd3))
    );

    // A load followed by no-load causes one increment from the loaded value.
    check_load_then_no_load_results_in_loaded_plus_one: assert property (
        @(posedge clk) (load ##1 !load) |=> (count == ($past(load_value, 2) + 4'd1))
    );

    // Two consecutive loads make the next-cycle sampled count equal the second load_value.
    check_two_consecutive_loads_results_in_second_value: assert property (
        @(posedge clk) (load ##1 load) |=> (count == $past(load_value))
    );
endmodule