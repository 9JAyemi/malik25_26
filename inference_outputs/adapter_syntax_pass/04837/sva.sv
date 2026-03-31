module counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [1:0] count
);

    // Reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 2'b00)
    );

    // When enabled below 3, count increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (count != 2'b11)) |=> (count == ($past(count) + 2'b01))
    );

    // When enabled at 3, count wraps to zero.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (count == 2'b11)) |=> (count == 2'b00)
    );

    // When disabled, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> (count == $past(count))
    );

endmodule