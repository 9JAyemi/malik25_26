module five_input_module_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic A1,
    input  logic A2,
    input  logic A3,
    input  logic B1,
    input  logic B2,
    input  logic Y
);
    // Y equals its defining boolean function.
    check_y_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ((A1 & A2) | (A1 & A3) | (B1 & B2))
    );

    // If A1 is 0, Y reduces to B1 & B2.
    check_y_when_A1_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b0) |-> (Y == (B1 & B2))
    );

    // If either B1 or B2 is 0, Y reduces to A1 & (A2 | A3).
    check_y_when_Bpair_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B1 == 1'b0) || (B2 == 1'b0)) |-> (Y == (A1 & (A2 | A3)))
    );

    // If A1 and (A2 or A3) are 1, Y must be 1.
    check_y_forced_high_by_A_path: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 & (A2 | A3)) |-> (Y == 1'b1)
    );

    // If B1 and B2 are 1, Y must be 1.
    check_y_forced_high_by_B_path: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 & B2) |-> (Y == 1'b1)
    );

    // If A2 and A3 are 0, Y reduces to B1 & B2.
    check_y_when_A2A3_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == (B1 & B2))
    );

    // If A2 and A3 are 1, Y equals A1 | (B1 & B2).
    check_y_when_A2A3_one: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A2 == 1'b1) && (A3 == 1'b1)) |-> (Y == (A1 | (B1 & B2)))
    );

    // If A2 is 0 and B2 is 0, Y reduces to A1 & A3.
    check_y_when_A2_zero_B2_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A2 == 1'b0) && (B2 == 1'b0)) |-> (Y == (A1 & A3))
    );

    // With all inputs stable across a cycle, Y must remain stable.
    check_y_stable_if_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2)) |-> $stable(Y)
    );

    // Any change on Y must be caused by a change on at least one input.
    check_y_changes_require_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> ($changed(A1) || $changed(A2) || $changed(A3) || $changed(B1) || $changed(B2))
    );
endmodule