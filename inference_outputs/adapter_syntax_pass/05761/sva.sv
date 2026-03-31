module my_2to1_mux_sva (
    input logic [16:0] MO,
    input logic [16:0] A,
    input logic [16:0] B,
    input logic        S
);

    // MO must always match the RTL mux expression.
    check_mux_function: assert property (
        @($global_clock) MO === ((S == 1'b1) ? B : A)
    );

    // When S is low, MO must select A.
    check_select_a_when_s_low: assert property (
        @($global_clock) (S === 1'b0) |-> (MO === A)
    );

    // When S is high, MO must select B.
    check_select_b_when_s_high: assert property (
        @($global_clock) (S === 1'b1) |-> (MO === B)
    );

    // If both data inputs are equal, MO must equal that common value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (A === B) |-> (MO === A)
    );

endmodule