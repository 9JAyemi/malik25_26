module dut_sva(
    input logic a,
    input logic b,
    input logic c,
    input logic true_val,
    input logic false_val,
    input logic and1,
    input logic and2,
    input logic and3,
    input logic or1,
    input logic or2,
    input logic or3,
    input logic not1,
    input logic not2
);

    // true_val is tied high.
    check_true_val_const: assert property (
        @($global_clock) (true_val === 1'b1)
    );

    // false_val is tied low.
    check_false_val_const: assert property (
        @($global_clock) (false_val === 1'b0)
    );

    // and1 matches a & b & c.
    check_and1_function: assert property (
        @($global_clock) (and1 === (a & b & c))
    );

    // and2 matches a & b.
    check_and2_function: assert property (
        @($global_clock) (and2 === (a & b))
    );

    // and3 matches a & c.
    check_and3_function: assert property (
        @($global_clock) (and3 === (a & c))
    );

    // or1 matches a | b | c.
    check_or1_function: assert property (
        @($global_clock) (or1 === (a | b | c))
    );

    // or2 matches a | b.
    check_or2_function: assert property (
        @($global_clock) (or2 === (a | b))
    );

    // or3 matches a | c.
    check_or3_function: assert property (
        @($global_clock) (or3 === (a | c))
    );

    // not1 matches logical negation of a.
    check_not1_function: assert property (
        @($global_clock) (not1 === (!a))
    );

    // not2 matches logical negation of b.
    check_not2_function: assert property (
        @($global_clock) (not2 === (!b))
    );

endmodule