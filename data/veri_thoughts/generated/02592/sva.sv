module five_to_one_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic Y
);
    // Analysis: no clock/reset in RTL; purely combinational; Y=1 if A|B|C or (D^E when A=B=C=0).

    // Y equals the combinational function encoded by the if/else chain.
    check_y_function_equivalence: assert property (
        @(posedge CLK) Y == (A || B || C || ((!A && !B && !C) && (D ^ E)))
    );

    // If any of A,B,C is 1, Y must be 1.
    check_y_high_when_any_abc: assert property (
        @(posedge CLK) (A || B || C) |-> (Y == 1'b1)
    );

    // If A,B,C are 0 and D^E is 1, Y must be 1.
    check_y_high_when_dxorE_no_abc: assert property (
        @(posedge CLK) (!A && !B && !C && (D ^ E)) |-> (Y == 1'b1)
    );

    // If A,B,C are 0 and D^E is 0, Y must be 0.
    check_y_low_when_no_conditions: assert property (
        @(posedge CLK) (!A && !B && !C && !(D ^ E)) |-> (Y == 1'b0)
    );

    // Y=1 only when one of the specified conditions holds.
    check_y_high_only_when_condition_true: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (A || B || C || ((!A && !B && !C) && (D ^ E)))
    );

    // Y=0 only when no condition in the chain is met.
    check_y_low_only_when_no_condition_true: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (!A && !B && !C && !(D ^ E))
    );

    // If inputs are stable across a cycle, Y must remain stable (combinational behavior).
    check_y_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D,E}) |-> $stable(Y)
    );
endmodule