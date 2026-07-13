module mux_2to1_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic S
);

    // Y must implement the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock) (Y === ((S == 1'b1) ? B : A))
    );

    // Y must follow B when S is high.
    check_select_b_when_s_high: assert property (
        @($global_clock) (S === 1'b1) |-> (Y === B)
    );

    // Y must follow A when S is low.
    check_select_a_when_s_low: assert property (
        @($global_clock) (S === 1'b0) |-> (Y === A)
    );

    // If both data inputs match, Y must match that common value.
    check_output_matches_equal_inputs: assert property (
        @($global_clock) (A === B) |-> (Y === A)
    );

endmodule