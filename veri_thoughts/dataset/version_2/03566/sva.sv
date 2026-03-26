module one_bit_adder_sva (
    input logic xi,
    input logic yi,
    input logic Si,
    input logic Co
);

    // Sum output must be the XOR of the two inputs.
    check_sum_matches_xor: assert property (
        @($global_clock) Si === (xi ^ yi)
    );

    // Carry output must be the AND of the two inputs.
    check_carry_matches_and: assert property (
        @($global_clock) Co === (xi & yi)
    );

    // Combined outputs must match 1-bit addition.
    check_outputs_match_addition: assert property (
        @($global_clock) {Co, Si} === ({1'b0, xi} + {1'b0, yi})
    );

    // Both low inputs must produce zero sum and zero carry.
    check_zero_plus_zero: assert property (
        @($global_clock) ((xi === 1'b0) && (yi === 1'b0)) |-> ((Si === 1'b0) && (Co === 1'b0))
    );

    // Mixed inputs must produce sum one and carry zero.
    check_mixed_inputs: assert property (
        @($global_clock) (((xi === 1'b0) && (yi === 1'b1)) || ((xi === 1'b1) && (yi === 1'b0)))
        |-> ((Si === 1'b1) && (Co === 1'b0))
    );

    // Both high inputs must produce sum zero and carry one.
    check_one_plus_one: assert property (
        @($global_clock) ((xi === 1'b1) && (yi === 1'b1)) |-> ((Si === 1'b0) && (Co === 1'b1))
    );

endmodule