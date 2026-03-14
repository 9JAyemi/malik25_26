module sky130_fd_sc_lp__nand3_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Combinational 3-input NAND with buffer: Y = ~(A & B & C). No clock/reset in RTL; use external CLK/RESETn.

    // Y matches 3-input NAND truth function.
    check_nand_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~(A & B & C)
    );

    // If A is 0, Y must be 1.
    check_y_high_when_A0: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0) |-> (Y == 1'b1)
    );

    // If B is 0, Y must be 1.
    check_y_high_when_B0: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b0) |-> (Y == 1'b1)
    );

    // If C is 0, Y must be 1.
    check_y_high_when_C0: assert property (
        @(posedge CLK) disable iff (!RESETn) (C == 1'b0) |-> (Y == 1'b1)
    );

    // If all inputs are 1, Y must be 0.
    check_y_low_when_all1: assert property (
        @(posedge CLK) disable iff (!RESETn) (A && B && C) |-> (Y == 1'b0)
    );

    // Y can be 0 only when all inputs are 1.
    check_y_zero_only_if_all1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b0) |-> (A && B && C)
    );

    // A falling edge on Y implies all inputs are 1 this cycle.
    check_y_fall_implies_all1: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(Y) |-> (A && B && C)
    );

    // A rising edge on Y implies at least one input is 0 this cycle.
    check_y_rise_implies_any0: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(Y) |-> ((A == 1'b0) || (B == 1'b0) || (C == 1'b0))
    );

    // If inputs are stable, Y must be stable.
    check_stable_inputs_imply_stable_y: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({A,B,C}) |-> $stable(Y)
    );

    // With B and C high and stable, a rising edge on A causes a falling edge on Y.
    check_y_fall_on_A_rise_with_BC_high_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($rose(A) && (B && C) && $past(B && C)) |-> $fell(Y)
    );
endmodule