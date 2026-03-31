module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    input logic [7:0] count
);

// Reset clears both outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (q == 8'h00) && (count == 8'h00)
    );

// q captures the 8-bit sum of d1 and d2 on the next clock.
    check_q_captures_sum: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q == ($past(d1) + $past(d2)))
    );

// count increments by one on the next clock when enabled.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 8'd1))
    );

// count holds its value on the next clock when not enabled.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !1'b1 |=> (count == $past(count))
    );

endmodule
