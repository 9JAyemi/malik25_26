module nand4_sva (
    input logic clk,
    input logic RESETn,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // Y equals D & ((A & B) | ~C)
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (!RESETn) Y == (D & ((A & B) | ~C))
    );

    // D=0 forces Y=0
    check_D_low_forces_Y_low: assert property (
        @(posedge clk) disable iff (!RESETn) (D == 1'b0) |-> (Y == 1'b0)
    );

    // C=0 makes Y follow D
    check_C_low_Y_follows_D: assert property (
        @(posedge clk) disable iff (!RESETn) (C == 1'b0) |-> (Y == D)
    );

    // C=1 makes Y == D & A & B
    check_C_high_Y_equals_D_and_A_and_B: assert property (
        @(posedge clk) disable iff (!RESETn) (C == 1'b1) |-> (Y == (D & A & B))
    );

    // A=1 and B=1 makes Y follow D
    check_A_and_B_high_Y_follows_D: assert property (
        @(posedge clk) disable iff (!RESETn) (A && B) |-> (Y == D)
    );

    // With C=1 and A=0, Y must be 0
    check_C_high_A_low_forces_Y_low: assert property (
        @(posedge clk) disable iff (!RESETn) (C && !A) |-> (Y == 1'b0)
    );

    // With C=1 and B=0, Y must be 0
    check_C_high_B_low_forces_Y_low: assert property (
        @(posedge clk) disable iff (!RESETn) (C && !B) |-> (Y == 1'b0)
    );

    // Y=1 implies D=1
    check_Y_high_implies_D_high: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == 1'b1) |-> (D == 1'b1)
    );

    // Y=1 with C=1 implies A=1 and B=1
    check_Y_high_with_C_high_implies_A_and_B_high: assert property (
        @(posedge clk) disable iff (!RESETn) (Y && C) |-> (A && B)
    );

    // If inputs are stable across cycles, Y is stable
    check_stable_inputs_hold_Y_stable: assert property (
        @(posedge clk) disable iff (!RESETn)
            ($past(RESETn) && (A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D == $past(D))) |-> (Y == $past(Y))
    );

    // With C held low, a rising D causes Y to rise
    check_D_rise_when_C_low_causes_Y_rise: assert property (
        @(posedge clk) disable iff (!RESETn)
            ($past(RESETn) && ($past(C) == 1'b0) && (C == 1'b0) && $rose(D)) |-> (Y == 1'b1)
    );

    // With C held low, a falling D causes Y to fall
    check_D_fall_when_C_low_causes_Y_fall: assert property (
        @(posedge clk) disable iff (!RESETn)
            ($past(RESETn) && ($past(C) == 1'b0) && (C == 1'b0) && $fell(D)) |-> (Y == 1'b0)
    );
endmodule