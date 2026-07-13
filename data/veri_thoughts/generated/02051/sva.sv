module mux_2_to_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y,
    input logic reg_A,
    input logic reg_B
);
    // Clock: clk (posedge). No reset. Sequential pipeline: reg_A/reg_B capture A/B; Y selects previous regs using current S.

    // reg_A equals previous-cycle A.
    check_regA_captures_A: assert property (
        @(posedge clk) $past(1'b1) |-> (reg_A == $past(A))
    );

    // reg_B equals previous-cycle B.
    check_regB_captures_B: assert property (
        @(posedge clk) $past(1'b1) |-> (reg_B == $past(B))
    );

    // Y equals previous-cycle selected reg using current S.
    check_Y_mux_prev_regs_with_curr_S: assert property (
        @(posedge clk) $past(1'b1) |-> (Y == (S ? $past(reg_B) : $past(reg_A)))
    );

    // When S==0, Y equals previous-cycle A.
    check_Y_prev_A_when_S0: assert property (
        @(posedge clk) ($past(1'b1) && (S == 1'b0)) |-> (Y == $past(A))
    );

    // When S==1, Y equals previous-cycle B.
    check_Y_prev_B_when_S1: assert property (
        @(posedge clk) ($past(1'b1) && (S == 1'b1)) |-> (Y == $past(B))
    );

    // On S rising edge, Y selects previous-cycle reg_B.
    check_Y_on_S_rise_selects_prev_regB: assert property (
        @(posedge clk) $rose(S) |-> (Y == $past(reg_B))
    );

    // On S falling edge, Y selects previous-cycle reg_A.
    check_Y_on_S_fall_selects_prev_regA: assert property (
        @(posedge clk) $fell(S) |-> (Y == $past(reg_A))
    );

    // Y equals mux of previous-cycle A/B using current S.
    check_Y_prev_data_based_on_curr_S: assert property (
        @(posedge clk) $past(1'b1) |-> (Y == (S ? $past(B) : $past(A)))
    );

endmodule