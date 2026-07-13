module counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic load,
    input logic [31:0] data_in,
    input logic [31:0] count
);

    // Count is zero while active-low reset is asserted.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst |-> (count == 32'd0)
    );

    // Load transfers data_in into count on the next clock.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        load |=> (count == $past(data_in))
    );

    // Load takes priority over enable when both are high.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        (load && en) |=> (count == $past(data_in))
    );

    // Enable increments count by one when load is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        (!load && en) |=> (count == ($past(count) + 32'd1))
    );

    // Count holds its value when load and enable are both low.
    check_idle_holds_count: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        (!load && !en) |=> (count == $past(count))
    );

endmodule