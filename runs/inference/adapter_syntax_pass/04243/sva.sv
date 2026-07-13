module mux2_sva (
    input logic A0,
    input logic A1,
    input logic S,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X must always match the mux equation.
    check_mux_function: assert property (
        @($global_clock) X == (S ? A1 : A0)
    );

    // When S is low, X must select A0.
    check_select_a0: assert property (
        @($global_clock) (S == 1'b0) |-> (X == A0)
    );

    // When S is high, X must select A1.
    check_select_a1: assert property (
        @($global_clock) (S == 1'b1) |-> (X == A1)
    );

    // If both data inputs are equal, X must match that common value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (A0 == A1) |-> (X == A0)
    );

endmodule