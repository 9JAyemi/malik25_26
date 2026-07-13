module binary_counter_sva (
    input logic       CLK,
    input logic       RESET,
    input logic [3:0] Q
);

    // Reset forces the counter output to zero.
    check_reset_clears_q: assert property (
        @(posedge CLK) !RESET |-> (Q == 4'b0000)
    );

    // Below 4'hF, the counter increments by one each active clock.
    check_count_increments: assert property (
        @(posedge CLK) disable iff (!RESET)
        (Q != 4'hF) |=> (Q == ($past(Q) + 4'd1))
    );

    // At 4'hF, the counter wraps back to zero on the next active clock.
    check_count_wraps: assert property (
        @(posedge CLK) disable iff (!RESET)
        (Q == 4'hF) |=> (Q == 4'h0)
    );

endmodule