module comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ,
    input logic GT
);

    // EQ must match the RTL's & of the inverted difference bits.
    check_eq_definition: assert property (
        @($global_clock) EQ == (&(~(A - B)))
    );

    // GT must match the RTL's comparison of the most-significant difference bit.
    check_gt_definition: assert property (
        @($global_clock) GT == ((A[3] - B[3]) & (~(A[3] - B[3])))
    );

    // EQ and GT cannot both be high.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !(EQ && GT)
    );

    // Equal inputs must drive EQ high and GT low.
    check_equal_inputs_outputs: assert property (
        @($global_clock) (A == B) |-> (EQ && !GT)
    );

    // A greater than B must drive GT high and EQ low.
    check_greater_than_inputs_outputs: assert property (
        @($global_clock) (A > B) |-> (!EQ && GT)
    );

    // A less than B must drive both outputs low.
    check_less_than_inputs_outputs: assert property (
        @($global_clock) (A < B) |-> (!EQ && !GT)
    );

endmodule