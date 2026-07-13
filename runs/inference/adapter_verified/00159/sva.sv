module top_module_sva (
    input logic clk,
    input logic reset,      // Asynchronous active-high reset
    input logic [3:0] q
);

// On reset, q is driven to 0 on the next clock.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

// When q is 15, it wraps to 0 on the next clock.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (q == 4'b1111) |=> (q == 4'b0000)
    );

// When q is not 15, it increments by 1 on the next clock.
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset) (q != 4'b1111) |=> (q == ($past(q) + 4'd1))
    );

// q can only be 0 or 15 on a sampled clock edge.
    q_only_zero_or_max: assert property (
        @(posedge clk) disable iff (reset) (q inside {4'b0000, 4'b1111})
    );

endmodule
