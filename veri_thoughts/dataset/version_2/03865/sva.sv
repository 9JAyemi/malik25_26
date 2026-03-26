module dff_async_reset_sva (
    input logic D,
    input logic RESET,
    input logic CLK,
    input logic Q
);

    // A sampled 1 on D is captured into Q on the next clock when reset stays low.
    check_capture_one: assert property (
        @(posedge CLK) disable iff (RESET) D |=> (Q == 1'b1)
    );

    // A sampled 0 on D is captured into Q on the next clock when reset stays low.
    check_capture_zero: assert property (
        @(posedge CLK) disable iff (RESET) !D |=> (Q == 1'b0)
    );

    // A reset seen on a clock keeps Q low at the following clock.
    check_reset_seen_on_clock_keeps_q_low: assert property (
        @(posedge CLK) RESET |=> (Q == 1'b0)
    );

    // A reset assertion between clocks clears Q by the next clock edge.
    check_async_reset_clears_q_by_next_clock: assert property (
        @(posedge RESET) 1'b1 |=> @(posedge CLK) (Q == 1'b0)
    );

endmodule