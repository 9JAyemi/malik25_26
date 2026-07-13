module counter_4bit_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] Q
);

    property p_count_increments;
        logic [3:0] q_prev;
        @(posedge clk) disable iff (!reset)
            (1'b1, q_prev = Q) |=> (Q == (q_prev + 4'd1));
    endproperty

    // Q is zero whenever reset is low.
    check_reset_clears_q_now: assert property (
        @(posedge clk) !reset |-> (Q == 4'b0000)
    );

    // Q is still zero on the next sampled clock after a reset-low cycle.
    check_reset_clears_q_next: assert property (
        @(posedge clk) !reset |=> (Q == 4'b0000)
    );

    // Without reset, Q increments by one each clock.
    check_count_increments: assert property (p_count_increments);

    // A count of 15 wraps to 0 on the next active clock.
    check_wraps_after_max: assert property (
        @(posedge clk) disable iff (!reset)
            (Q == 4'hF) |=> (Q == 4'h0)
    );

    // A count of 0 advances to 1 on the next active clock.
    check_zero_to_one: assert property (
        @(posedge clk) disable iff (!reset)
            (Q == 4'h0) |=> (Q == 4'h1)
    );

endmodule