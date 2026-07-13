module dffl_64_sva (
    input logic        clk,
    input logic        ld,
    input logic        rst,
    input logic [63:0] d,
    input logic [63:0] q
);

// Reset clears q on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 64'h0)
    );

// Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (rst && ld) |=> (q == 64'h0)
    );

// Load captures d when reset is low.
    check_load_captures_d: assert property (
        @(posedge clk) disable iff (rst) ld |=> (q == $past(d))
    );

// When neither reset nor load is asserted, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (rst) (!ld) |=> (q == $past(q))
    );

endmodule
