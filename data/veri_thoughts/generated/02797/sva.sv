module xor4_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] X
);
    // X equals bitwise XOR of A and B each cycle.
    check_xor_function: assert property (
        @(posedge clk) X === (A ^ B)
    );

    // If A and B are stable across a cycle, X remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(X)
    );

    // If X changes, at least one of A or B must have changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A) || $changed(B))
    );

    // With B stable, X's delta equals A's delta.
    check_delta_matches_A_when_B_stable: assert property (
        @(posedge clk) $stable(B) |-> ((X ^ $past(X)) === (A ^ $past(A)))
    );

    // With A stable, X's delta equals B's delta.
    check_delta_matches_B_when_A_stable: assert property (
        @(posedge clk) $stable(A) |-> ((X ^ $past(X)) === (B ^ $past(B)))
    );
endmodule