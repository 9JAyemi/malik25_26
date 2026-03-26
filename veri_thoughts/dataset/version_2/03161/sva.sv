module sky130_fd_sc_lp__udp_mux_2to1_N_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic Y,
    input logic S
);

    // Y matches the implemented 2:1 mux equation.
    check_mux_function: assert property (
        @(posedge clk) Y === ((~S & A0) | (S & A1))
    );

    // When S is low, Y selects A0.
    check_select_a0: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A0)
    );

    // When S is high, Y selects A1.
    check_select_a1: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === A1)
    );

    // If both data inputs are low, Y is low.
    check_both_zero_force_zero: assert property (
        @(posedge clk) ((A0 === 1'b0) && (A1 === 1'b0)) |-> (Y === 1'b0)
    );

    // A1 changes do not affect Y when A0 is selected and stable.
    check_unselected_a1_no_effect: assert property (
        @(posedge clk) ((S === 1'b0) && $stable(S) && $stable(A0) && $changed(A1)) |-> $stable(Y)
    );

    // A0 changes do not affect Y when A1 is selected and stable.
    check_unselected_a0_no_effect: assert property (
        @(posedge clk) ((S === 1'b1) && $stable(S) && $stable(A1) && $changed(A0)) |-> $stable(Y)
    );

endmodule