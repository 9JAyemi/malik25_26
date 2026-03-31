module sysgen_logical_8b7810a2aa_sva (
    input logic d0,
    input logic d1,
    input logic y,
    input logic clk,
    input logic ce,
    input logic clr
);
    // y equals d0 OR d1 every cycle.
    check_y_equals_or: assert property (
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
    check_y_zero_implies_inputs_zero: assert property (
        @(posedge clk) disable iff (clr) !y |-> (!d0 && !d1)
    );

    // If y is 1, at least one of d0 or d1 must be 1.
    check_y_one_implies_some_input_one: assert property (
        @(posedge clk) disable iff (clr) y |-> (d0 || d1)
    );

    // With ce=1 and d0=0,d1=0, y must be 0 on the next cycle.
    check_next_cycle_zero_when_ce1_inputs_zero: assert property (
        @(posedge clk) disable iff (clr) (ce && !d0 && !d1) |=> !y
    );

    // With ce=1 and d0=1,d1=0, y must be 1 on the next cycle.
    check_next_cycle_one_when_ce1_d01_d10: assert property (
        @(posedge clk) disable iff (clr) (ce && d0 && !d1) |=> y
    );

    // With ce=1 and d0=0,d1=1, y must be 1 on the next cycle.
    check_next_cycle_one_when_ce1_d00_d11: assert property (
        @(posedge clk) disable iff (clr) (ce && !d0 && d1) |=> y
    );

    // With ce=1 and d0=1,d1=1, y must be 1 on the next cycle.
    check_next_cycle_one_when_ce1_inputs_one: assert property (
        @(posedge clk) disable iff (clr) (ce && d0 && d1) |=> y
    );
endmodule