module sysgen_logical_8b7810a2aa_sva (
    input logic d0,
    input logic d1,
    input logic y,
    input logic clk,
    input logic ce,
    input logic clr
);

// y equals d0 OR d1 every cycle.
    check_y_matches_or: assert property (
        @(posedge clk) disable iff (clr) y == (d0 | d1)
    );

// If d0 is 1, y must be 1.
    check_y_high_when_d0_high: assert property (
        @(posedge clk) disable iff (clr) d0 |-> y
    );

// If d1 is 1, y must be 1.
    check_y_high_when_d1_high: assert property (
        @(posedge clk) disable iff (clr) d1 |-> y
    );

// If both d0 and d1 are 0, y must be 0.
    check_y_low_when_both_zero: assert property (
        @(posedge clk) disable iff (clr) (!d0 && !d1) |-> !y
    );

// If y is 0, both d0 and d1 must be 0.
    check_inputs_zero_when_y_zero: assert property (
        @(posedge clk) disable iff (clr) !y |-> (!d0 && !d1)
    );

// If y is 1, at least one of d0 or d1 must be 1.
    check_inputs_nonzero_when_y_one: assert property (
        @(posedge clk) disable iff (clr) y |-> (d0 || d1)
    );

endmodule
