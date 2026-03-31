module mux2_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

// X must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) X == ((S == 1'b1) ? A1 : A0)
    );

// When S is low, X must follow A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) (S == 1'b0) |-> (X == A0)
    );

// When S is high, X must follow A1.
    check_select_high_routes_a1: assert property (
        @(posedge clk) (S == 1'b1) |-> (X == A1)
    );

// Equal data inputs must force X to that value regardless of S.
    check_equal_inputs_force_x: assert property (
        @(posedge clk) (A0 == A1) |-> (X == A0)
    );

endmodule
