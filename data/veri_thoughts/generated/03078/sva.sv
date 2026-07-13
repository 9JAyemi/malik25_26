module top_module_assertions (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  d,
    input logic        sel_b1,
    input logic        sel_b2,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  q
);

    // Synchronous reset clears q by the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 8'b0)
    );

    // q remains zero while reset stays asserted.
    check_q_zero_during_held_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (q == 8'b0)
    );

    // On consecutive non-reset cycles, q equals the prior cycle's d.
    check_q_captures_d: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (q == $past(d))
    );

    // If d is unchanged across non-reset cycles, q stays unchanged.
    check_q_holds_when_d_holds: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && (d == $past(d)) |=> (q == $past(q))
    );

endmodule