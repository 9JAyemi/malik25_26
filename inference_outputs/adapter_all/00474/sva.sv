module XOR_M_sva (
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic Sgn_Info
);

    // Sgn_Info must always equal the XOR of Sgn_X and Sgn_Y.
    check_xor_function: assert property (
        @($global_clock) Sgn_Info == (Sgn_X ^ Sgn_Y)
    );

    // When both inputs are low, the output must be low.
    check_both_low: assert property (
        @($global_clock) (!Sgn_X && !Sgn_Y) |-> !Sgn_Info
    );

    // When both inputs are high, the output must be low.
    check_both_high: assert property (
        @($global_clock) (Sgn_X && Sgn_Y) |-> !Sgn_Info
    );

    // When the inputs differ, the output must be high.
    check_inputs_differ: assert property (
        @($global_clock) (Sgn_X ^ Sgn_Y) |-> Sgn_Info
    );

endmodule