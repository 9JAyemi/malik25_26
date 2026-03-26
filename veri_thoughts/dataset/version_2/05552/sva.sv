module dff_4_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] d,
    input logic [3:0] q
);

    // Reset clears q on the following clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // q stays zero across consecutive reset cycles.
    check_reset_holds_q_zero: assert property (
        @(posedge clk) reset ##1 reset |-> (q == 4'b0000)
    );

    // q is still zero on the clock where reset deasserts.
    check_reset_release_observes_zero: assert property (
        @(posedge clk) $fell(reset) |-> (q == 4'b0000)
    );

    // When not in reset, q captures d on the next clock.
    check_q_captures_d: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q == $past(d))
    );

endmodule