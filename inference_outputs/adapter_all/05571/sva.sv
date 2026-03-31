module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    input logic [7:0] count
);

    // Reset clears both registered outputs by the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> ((q == 8'h00) && (count == 8'h00))
    );

    // The register captures the sum of d1 and d2 on each enabled cycle.
    check_register_captures_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q == $past(d1 + d2))
    );

    // The counter increments by one on each enabled cycle.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == ($past(count) + 8'd1))
    );

    // The register holds its value when enable is low.
    check_register_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !1'b1 |=> (q == $past(q))
    );

    // The counter holds its value when enable is low.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !1'b1 |=> (count == $past(count))
    );

endmodule