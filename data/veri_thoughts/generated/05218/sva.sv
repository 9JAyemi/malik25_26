module mux_2to1_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic SEL,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must always match the mux equation.
    check_mux_function: assert property (
        @($global_clock) Y === (SEL ? B : A)
    );

    // When SEL is low, Y must follow A.
    check_select_low_routes_a: assert property (
        @($global_clock) (SEL === 1'b0) |-> (Y === A)
    );

    // When SEL is high, Y must follow B.
    check_select_high_routes_b: assert property (
        @($global_clock) (SEL === 1'b1) |-> (Y === B)
    );

    // When A and B are equal, Y must equal that shared value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (A === B) |-> (Y === A)
    );

endmodule