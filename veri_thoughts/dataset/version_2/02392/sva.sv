module sky130_fd_sc_hd__o21ai_sva (
    input  logic CLK,  // verification clock (RTL has no clock/reset)
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1
);
    // Function: Y = ~(B1 & (A1 | A2))

    // Y must equal the combinational function.
    check_function_equivalence: assert property (
        @(posedge CLK) Y == ~(B1 & (A1 | A2))
    );

    // B1 low forces Y high.
    check_B1_low_forces_Y_high: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A1 and A2 low force Y high.
    check_A_both_low_forces_Y_high: assert property (
        @(posedge CLK) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // B1 high and any A high force Y low.
    check_B1_high_and_any_A_high_forces_Y_low: assert property (
        @(posedge CLK) (B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 high with both A low forces Y high.
    check_B1_high_and_A_both_low_forces_Y_high: assert property (
        @(posedge CLK) (B1 == 1'b1) && (A1 == 1'b0) && (A2 == 1'b0) |-> (Y == 1'b1)
    );

    // If inputs are stable, Y must be stable (pure combinational).
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A1) && $stable(A2) && $stable(B1) |-> $stable(Y)
    );

    // Y low implies B1 is high and at least one A is high.
    check_Y_low_implies_inputs_conditions: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1))
    );

    // Y high implies B1 is low or both A are low.
    check_Y_high_implies_inputs_conditions: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((B1 == 1'b0) || ((A1 == 1'b0) && (A2 == 1'b0)))
    );

    // Rising B1 with any A high drives Y low.
    check_rise_B1_with_any_A_high: assert property (
        @(posedge CLK) $rose(B1) && ((A1 == 1'b1) || (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // Rising B1 with both A low drives Y high.
    check_rise_B1_with_A_both_low: assert property (
        @(posedge CLK) $rose(B1) && (A1 == 1'b0) && (A2 == 1'b0) |-> (Y == 1'b1)
    );
endmodule