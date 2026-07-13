module mux_4to2_sva (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic EN
);

    // When disabled, the output must be forced low.
    check_disable_forces_zero: assert property (
        @(posedge clk) (EN == 1'b1) |-> (X == 1'b0)
    );

    // When enabled with select 00, X must follow A0.
    check_select_a0_when_enabled: assert property (
        @(posedge clk) (EN == 1'b0 && S0 == 1'b0 && S1 == 1'b0) |-> (X == A0)
    );

    // When enabled with select 01, X must follow A1.
    check_select_a1_when_enabled: assert property (
        @(posedge clk) (EN == 1'b0 && S0 == 1'b0 && S1 == 1'b1) |-> (X == A1)
    );

    // When enabled with select 10, X must follow A2.
    check_select_a2_when_enabled: assert property (
        @(posedge clk) (EN == 1'b0 && S0 == 1'b1 && S1 == 1'b0) |-> (X == A2)
    );

    // When enabled with select 11, X must follow A3.
    check_select_a3_when_enabled: assert property (
        @(posedge clk) (EN == 1'b0 && S0 == 1'b1 && S1 == 1'b1) |-> (X == A3)
    );

    // X must always match the implemented mux equation.
    check_output_matches_mux_equation: assert property (
        @(posedge clk)
        X == ((EN == 1'b0) ? ((S0 & S1) ? A3 : (S0 ? A2 : (S1 ? A1 : A0))) : 1'b0)
    );

endmodule