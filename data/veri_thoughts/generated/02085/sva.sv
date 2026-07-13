module sky130_fd_sc_lp__a21oi_4_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND
);
    // Y equals ~( (~A1 & A2) | B1 ).
    check_function_equation: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~((~A1 & A2) | B1)
    );

    // B1 high forces Y low.
    check_B1_high_forces_Y_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1 high and B1 low force Y high.
    check_A1_high_B1_low_forces_Y_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b1 && B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A2 low and B1 low force Y high.
    check_A2_low_B1_low_forces_Y_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A2 == 1'b0 && B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A1 low and A2 high force Y low.
    check_A1_low_A2_high_forces_Y_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b0 && A2 == 1'b1) |-> (Y == 1'b0)
    );

    // If B1 low and Y low, then A1 low and A2 high.
    check_B1_low_Y_low_implies_A1_low_A2_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b0 && Y == 1'b0) |-> (A1 == 1'b0 && A2 == 1'b1)
    );

    // When B1 low, Y equals (A1 or ~A2).
    check_B1_low_equation_simplified: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b0) |-> (Y == (A1 | ~A2))
    );

    // When A1 low, Y equals ~(A2 or B1).
    check_A1_low_equation_simplified: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b0) |-> (Y == ~(A2 | B1))
    );

    // When A2 high, Y equals (A1 & ~B1).
    check_A2_high_equation_simplified: assert property (
        @(posedge CLK) disable iff (!RESETn) (A2 == 1'b1) |-> (Y == (A1 & ~B1))
    );

    // If Y high, then B1 low and (A1 high or A2 low).
    check_Y_high_condition_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b1) |-> (B1 == 1'b0 && (A1 == 1'b1 || A2 == 1'b0))
    );
endmodule