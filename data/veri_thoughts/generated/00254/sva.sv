module addition_module_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] Sum
);

    // Sum always equals the zero-extended addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) Sum == ({1'b0, A} + {1'b0, B})
    );

    // If both inputs stay the same between samples, Sum also stays the same.
    check_stable_inputs_hold_sum: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(Sum)
    );

endmodule