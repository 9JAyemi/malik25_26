module Comparator_sva #(
    parameter int n = 8
) (
    input  logic                  CLK,
    input  logic [n-1:0]          a,
    input  logic [n-1:0]          b,
    input  logic [1:0]            ctrl,
    input  logic                  out,
    input  logic signed [n-1:0]   a_signed,
    input  logic signed [n-1:0]   b_signed
);
    // Equality mode: out reflects (a == b).
    check_eq_mode_out: assert property (
        @(posedge CLK) (ctrl == 2'b00) |-> (out == (a == b))
    );

    // Greater-than mode: out reflects (a_signed > b_signed).
    check_gt_mode_out: assert property (
        @(posedge CLK) (ctrl == 2'b01) |-> (out == (a_signed > b_signed))
    );

    // Less-than mode: out reflects (a_signed < b_signed).
    check_lt_mode_out: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (out == (a_signed < b_signed))
    );

    // Default/other mode (2'b11): out is 0.
    check_default_zero: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (out == 1'b0)
    );

    // When comparing (01/10), a_signed equals a due to truncation of concatenation.
    check_compare_mode_a_assigned: assert property (
        @(posedge CLK) (ctrl inside {2'b01,2'b10}) |-> (a_signed == a)
    );

    // When comparing (01/10), b_signed equals b due to truncation of concatenation.
    check_compare_mode_b_assigned: assert property (
        @(posedge CLK) (ctrl inside {2'b01,2'b10}) |-> (b_signed == b)
    );

    // When not comparing (00/11) and ctrl stable, a_signed holds its value (latch behavior).
    check_hold_a_when_not_compare: assert property (
        @(posedge CLK) (ctrl inside {2'b00,2'b11} && $stable(ctrl)) |-> $stable(a_signed)
    );

    // When not comparing (00/11) and ctrl stable, b_signed holds its value (latch behavior).
    check_hold_b_when_not_compare: assert property (
        @(posedge CLK) (ctrl inside {2'b00,2'b11} && $stable(ctrl)) |-> $stable(b_signed)
    );

    // When comparing and inputs/ctrl stable, a_signed remains stable.
    check_compare_stable_a: assert property (
        @(posedge CLK) (ctrl inside {2'b01,2'b10} && $stable(ctrl) && $stable(a)) |-> $stable(a_signed)
    );

    // When comparing and inputs/ctrl stable, b_signed remains stable.
    check_compare_stable_b: assert property (
        @(posedge CLK) (ctrl inside {2'b01,2'b10} && $stable(ctrl) && $stable(b)) |-> $stable(b_signed)
    );
endmodule