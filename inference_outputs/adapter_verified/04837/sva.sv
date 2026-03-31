module counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [1:0] count
);

// Reset drives count to 0 on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |=> (count == 2'b00)
    );

// When enabled below 3, count increments by 1.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (count != 2'b11)) |=> (count == ($past(count) + 2'b01))
    );

// When enabled at 3, count wraps to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst)
        (en && (count == 2'b11)) |=> (count == 2'b00)
    );

// When disabled, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!rst)
        (!en) |=> (count == $past(count))
    );

endmodule
