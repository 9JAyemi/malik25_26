module comparator_assertions (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic eq,
    input logic gt,
    input logic lt
);

    // No explicit clock or reset exists in the RTL; use the global clock.
    // Logic is purely combinational.

    // eq must match the equality comparison of the two inputs.
    check_eq_definition: assert property (
        @($global_clock) eq === (in0 == in1)
    );

    // gt must match the unsigned greater-than comparison of the two inputs.
    check_gt_definition: assert property (
        @($global_clock) gt === (in0 > in1)
    );

    // lt must match the unsigned less-than comparison of the two inputs.
    check_lt_definition: assert property (
        @($global_clock) lt === (in0 < in1)
    );

    // When eq is asserted, gt and lt must both be deasserted.
    check_eq_excludes_gt_lt: assert property (
        @($global_clock) eq |-> (!gt && !lt)
    );

    // When gt is asserted, eq and lt must both be deasserted.
    check_gt_excludes_eq_lt: assert property (
        @($global_clock) gt |-> (!eq && !lt)
    );

    // When lt is asserted, eq and gt must both be deasserted.
    check_lt_excludes_eq_gt: assert property (
        @($global_clock) lt |-> (!eq && !gt)
    );

endmodule