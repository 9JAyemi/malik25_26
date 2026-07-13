module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // A sampled 1 reaches q three clocks later.
    check_sampled_one_delayed_three: assert property (
        @(posedge clk) d |-> ##3 q
    );

    // A sampled 0 reaches q three clocks later.
    check_sampled_zero_delayed_three: assert property (
        @(posedge clk) !d |-> ##3 !q
    );

    // Three consecutive 1s propagate to q three cycles later.
    check_run_of_ones_propagates: assert property (
        @(posedge clk) (d ##1 d ##1 d) |=> (q ##1 q ##1 q)
    );

    // Three consecutive 0s propagate to q three cycles later.
    check_run_of_zeros_propagates: assert property (
        @(posedge clk) (!d ##1 !d ##1 !d) |=> (!q ##1 !q ##1 !q)
    );

    // An alternating 1-0-1 input pattern propagates to q.
    check_pattern_101_propagates: assert property (
        @(posedge clk) (d ##1 !d ##1 d) |=> (q ##1 !q ##1 q)
    );

    // An alternating 0-1-0 input pattern propagates to q.
    check_pattern_010_propagates: assert property (
        @(posedge clk) (!d ##1 d ##1 !d) |=> (!q ##1 q ##1 !q)
    );

endmodule