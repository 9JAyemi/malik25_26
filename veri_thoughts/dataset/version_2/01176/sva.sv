module sky130_fd_sc_hs__counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic load,
    input logic [31:0] count_max,
    input logic [31:0] count
);
    // On load, next count equals previous count_max.
    check_load_sets_count_to_max: assert property (
        @(posedge clk) disable iff (rst)
            load |=> (count == $past(count_max))
    );

    // Load has priority over enable when both are high.
    check_load_overrides_enable: assert property (
        @(posedge clk) disable iff (rst)
            (load && enable) |=> (count == $past(count_max))
    );

    // When enabled without load, next count either wraps to 0 at max or increments by 1.
    check_enable_behavior: assert property (
        @(posedge clk) disable iff (rst)
            (!load && enable) |=> (
                (($past(count) == $past(count_max)) && (count == '0)) ||
                (($past(count) != $past(count_max)) && (count == $past(count) + 1))
            )
    );

    // When idle (no load and not enabled), count holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst)
            (!load && !enable) |=> (count == $past(count))
    );

    // When enabled and not at max (and no load), count increments by 1.
    check_enable_increments_nonmax: assert property (
        @(posedge clk) disable iff (rst)
            (!load && enable && (count != count_max)) |=> (count == $past(count) + 1)
    );

    // When enabled and at max (and no load), count wraps to 0.
    check_enable_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst)
            (!load && enable && (count == count_max)) |=> (count == '0)
    );
endmodule