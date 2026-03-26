module binary_counter_sva
#(
    parameter WIDTH = 4
)
(
    input logic clk,
    input logic rst,
    input logic en,
    input logic load,
    input logic [WIDTH-1:0] data,
    input logic [WIDTH-1:0] count,
    input logic max_flag
);

    // Reset clears the count and deasserts max_flag.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        !rst |-> ((count == {WIDTH{1'b0}}) && (max_flag == 1'b0))
    );

    // max_flag must match whether count is all ones.
    check_max_flag_matches_count: assert property (
        @(posedge clk) disable iff (!rst)
        (max_flag == (count == {WIDTH{1'b1}}))
    );

    // load updates count with data on the next cycle.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!rst)
        load |=> (count == $past(data))
    );

    // load determines max_flag from the loaded data on the next cycle.
    check_load_updates_max_flag: assert property (
        @(posedge clk) disable iff (!rst)
        load |=> (max_flag == ($past(data) == {WIDTH{1'b1}}))
    );

    // load has priority over enable when both are asserted.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (!rst)
        (load && en) |=> (count == $past(data))
    );

    // enable increments count when load is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (!rst)
        (en && !load) |=> (count == ($past(count) + 1'b1))
    );

    // Incrementing from the maximum value wraps count to zero.
    check_enable_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (en && !load && (count == {WIDTH{1'b1}})) |=> ((count == {WIDTH{1'b0}}) && (max_flag == 1'b0))
    );

    // Without load or enable, count holds its value.
    check_idle_holds_count: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && !en) |=> (count == $past(count))
    );

endmodule