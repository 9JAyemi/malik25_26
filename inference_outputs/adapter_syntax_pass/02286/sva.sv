module sysgen_logical_8b7810a2aa_sva (
    input logic d0,
    input logic d1,
    input logic y,
    input logic clk,
    input logic ce,
    input logic clr
);

    // y must always equal the OR of d0 and d1.
    check_y_matches_or: assert property (
        @(posedge clk) disable iff (clr) y == (d0 | d1)
    );

    // A high d0 must force y high.
    check_d0_high_sets_y: assert property (
        @(posedge clk) disable iff (clr) d0 |-> y
    );

    // A high d1 must force y high.
    check_d1_high_sets_y: assert property (
        @(posedge clk) disable iff (clr) d1 |-> y
    );

    // A low d0 and d1 must force y low.
    check_both_inputs_low_clear_y: assert property (
        @(posedge clk) disable iff (clr) (!d0 && !d1) |-> !y
    );

    // A high y must come from at least one high input.
    check_y_high_has_valid_cause: assert property (
        @(posedge clk) disable iff (clr) y |-> (d0 || d1)
    );

endmodule