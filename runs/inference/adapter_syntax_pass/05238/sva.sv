module my_or2_8_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must match the implemented OR-with-C-inversion function.
    check_output_function: assert property (
        @($global_clock) X == (C ? ~(A | B) : (A | B))
    );

    // When C is low, X must equal A OR B.
    check_c_low_or_mode: assert property (
        @($global_clock) !C |-> (X == (A | B))
    );

    // When C is high, X must equal the inverted OR of A and B.
    check_c_high_inverted_or_mode: assert property (
        @($global_clock) C |-> (X == ~(A | B))
    );

    // If both OR inputs are low, X must be low.
    check_or_inputs_low: assert property (
        @($global_clock) (!A && !B) |-> !X
    );

    // If either OR input is high, X must be high.
    check_or_inputs_high: assert property (
        @($global_clock) (A || B) |-> X
    );

    // If C is high and both OR inputs are low, X must be high.
    check_c_high_and_or_inputs_low: assert property (
        @($global_clock) (C && !A && !B) |-> X
    );

    // If C is high and either OR input is high, X must be low.
    check_c_high_and_or_inputs_high: assert property (
        @($global_clock) (C && (A || B)) |-> !X
    );

endmodule