module two_input_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y matches the RTL boolean equation.
    check_output_equation: assert property (
        @(posedge clk) Y == ~((~A & B) | (A & ~B))
    );

    // 00 on the inputs drives Y high.
    check_00_high: assert property (
        @(posedge clk) (!A && !B) |-> (Y == 1'b1)
    );

    // 01 on the inputs drives Y low.
    check_01_low: assert property (
        @(posedge clk) (!A && B) |-> (Y == 1'b0)
    );

    // 10 on the inputs drives Y low.
    check_10_low: assert property (
        @(posedge clk) (A && !B) |-> (Y == 1'b0)
    );

    // 11 on the inputs drives Y high.
    check_11_high: assert property (
        @(posedge clk) (A && B) |-> (Y == 1'b1)
    );

    // Stable sampled inputs keep the sampled output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

endmodule