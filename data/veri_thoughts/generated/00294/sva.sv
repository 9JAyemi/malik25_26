module counter_sva (
    input logic       CLK,
    input logic       RST,
    input logic       enable,
    input logic [3:0] count_out
);

    // Reset clears the counter.
    check_reset_clears_count: assert property (
        @(posedge CLK) RST |=> (count_out == 4'b0000)
    );

    // When enabled outside reset, the counter increments by one.
    check_enable_increments_count: assert property (
        @(posedge CLK) disable iff (RST)
        enable |=> (count_out == ($past(count_out) + 4'b0001))
    );

    // When disabled outside reset, the counter holds its value.
    check_disable_holds_count: assert property (
        @(posedge CLK) disable iff (RST)
        !enable |=> (count_out == $past(count_out))
    );

    // Counting from 4'hF wraps the counter to 4'h0.
    check_wraps_after_max: assert property (
        @(posedge CLK) disable iff (RST)
        (enable && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );

    // Reset takes priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge CLK)
        (RST && enable) |=> (count_out == 4'b0000)
    );

endmodule