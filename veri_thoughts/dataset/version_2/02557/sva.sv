module signal_combiner_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals (A|B|C|D) masked off when all inputs are 1
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((A | B | C | D) & ~(A & B & C & D))
    );

    // All inputs 1 forces X to 0
    check_all_ones_forces_zero: assert property (
        @(posedge CLK) (A & B & C & D) |-> (X == 1'b0)
    );

    // All inputs 0 forces X to 0
    check_all_zeros_forces_zero: assert property (
        @(posedge CLK) !(A | B | C | D) |-> (X == 1'b0)
    );

    // When not all ones, X equals the OR of inputs
    check_not_all_ones_equals_or: assert property (
        @(posedge CLK) !(A & B & C & D) |-> (X == (A | B | C | D))
    );

    // If some but not all inputs are 1, X is 1
    check_partial_ones_give_one: assert property (
        @(posedge CLK) ((A | B | C | D) && !(A & B & C & D)) |-> (X == 1'b1)
    );

    // X high implies at least one input high and not all inputs high
    check_x_high_condition: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A | B | C | D) && !(A & B & C & D))
    );

    // X low occurs only when all zeros or all ones
    check_x_low_only_allzeros_or_allones: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((!(A | B | C | D)) || (A & B & C & D))
    );

    // Exactly one-hot on A drives X high
    check_singleton_A: assert property (
        @(posedge CLK) (A && !B && !C && !D) |-> (X == 1'b1)
    );

    // Exactly one-hot on B drives X high
    check_singleton_B: assert property (
        @(posedge CLK) (!A && B && !C && !D) |-> (X == 1'b1)
    );

    // Exactly one-hot on C drives X high
    check_singleton_C: assert property (
        @(posedge CLK) (!A && !B && C && !D) |-> (X == 1'b1)
    );

    // Exactly one-hot on D drives X high
    check_singleton_D: assert property (
        @(posedge CLK) (!A && !B && !C && D) |-> (X == 1'b1)
    );
endmodule