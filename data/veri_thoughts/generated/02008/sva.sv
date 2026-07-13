module nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);
    ///// Combinational function checks /////
    // Y must equal OR of inputs per gate structure.
    check_y_is_or: assert property (
        @(posedge clk) Y == (A || B || C_N || D_N)
    );

    // Y cannot be HIGH unless some input is HIGH.
    check_no_false_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A || B || C_N || D_N)
    );

    // When all inputs are LOW, Y must be LOW.
    check_all_low_implies_y_low: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && C_N == 1'b0 && D_N == 1'b0) |-> (Y == 1'b0)
    );

    // Y is LOW only if all inputs are LOW (no other way to get 0 on OR).
    check_y_low_only_if_all_low: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A == 1'b0 && B == 1'b0 && C_N == 1'b0 && D_N == 1'b0)
    );

    // A being HIGH forces Y HIGH.
    check_A_dominates: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b1)
    );

    // B being HIGH forces Y HIGH.
    check_B_dominates: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == 1'b1)
    );

    // C_N being HIGH forces Y HIGH.
    check_C_N_dominates: assert property (
        @(posedge clk) (C_N == 1'b1) |-> (Y == 1'b1)
    );

    // D_N being HIGH forces Y HIGH.
    check_D_N_dominates: assert property (
        @(posedge clk) (D_N == 1'b1) |-> (Y == 1'b1)
    );

    ///// Edge-sensitive sanity checks /////
    // A rising edge on Y implies some input is HIGH in that cycle.
    check_y_rise_requires_input_high: assert property (
        @(posedge clk) $rose(Y) |-> (A || B || C_N || D_N)
    );

    // A falling edge on Y implies all inputs are LOW in that cycle.
    check_y_fall_requires_all_low: assert property (
        @(posedge clk) $fell(Y) |-> (A == 1'b0 && B == 1'b0 && C_N == 1'b0 && D_N == 1'b0)
    );
endmodule