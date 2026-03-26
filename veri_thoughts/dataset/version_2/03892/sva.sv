module bin_counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Any reset event leaves the counter cleared by the next observed edge.
    check_reset_clears_count: assert property (
        @(posedge clk or posedge reset) reset |=> (count == 4'b0000)
    );

    // When enabled outside reset, the counter increments by one.
    check_enable_increments_count: assert property (
        @(posedge clk or posedge reset) disable iff (reset)
        enable |=> (count == ($past(count) + 4'd1))
    );

    // When disabled outside reset, the counter holds its value.
    check_disable_holds_count: assert property (
        @(posedge clk or posedge reset) disable iff (reset)
        !enable |=> $stable(count)
    );

    // When 15 is enabled outside reset, the counter wraps to zero.
    check_wraps_from_f_to_zero: assert property (
        @(posedge clk or posedge reset) disable iff (reset)
        (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule