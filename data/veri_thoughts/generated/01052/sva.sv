module and4_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals the bitwise AND of A, B, C, and D.
    check_and_equation: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // X can be HIGH only if all inputs are HIGH.
    check_x_high_requires_all_high: assert property (
        @(posedge clk) X |-> (A && B && C && D)
    );

    // All inputs HIGH implies X is HIGH.
    check_all_high_implies_x_high: assert property (
        @(posedge clk) (A && B && C && D) |-> X
    );

    // A LOW forces X LOW.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (!A) |-> (!X)
    );

    // B LOW forces X LOW.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) (!B) |-> (!X)
    );

    // C LOW forces X LOW.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) (!C) |-> (!X)
    );

    // D LOW forces X LOW.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) (!D) |-> (!X)
    );

    // X rising edge only when all inputs are HIGH.
    check_x_rise_requires_all_high: assert property (
        @(posedge clk) $rose(X) |-> (A && B && C && D)
    );

    // X falling edge implies at least one input is LOW.
    check_x_fall_requires_any_low: assert property (
        @(posedge clk) $fell(X) |-> (!A || !B || !C || !D)
    );
endmodule