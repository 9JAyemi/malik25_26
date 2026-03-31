module sky130_fd_sc_hd__xor2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // X must equal the XOR of A and B.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // When A and B are equal, X must be low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (A == B) |-> (X == 1'b0)
    );

    // When A and B differ, X must be high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (A != B) |-> (X == 1'b1)
    );

    // X can only change when at least one input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A) || $changed(B))
    );

    // With B stable, a change on A must change X.
    check_a_change_affects_x_when_b_stable: assert property (
        @(posedge clk) ($changed(A) && $stable(B)) |-> $changed(X)
    );

    // With A stable, a change on B must change X.
    check_b_change_affects_x_when_a_stable: assert property (
        @(posedge clk) ($changed(B) && $stable(A)) |-> $changed(X)
    );

    // With A stable, a change on X must reflect B.
    check_x_change_reflects_b_when_a_stable: assert property (
        @(posedge clk) ($changed(X) && $stable(A)) |-> (X == B)
    );

    // With B stable, a change on X must reflect A.
    check_x_change_reflects_a_when_b_stable: assert property (
        @(posedge clk) ($changed(X) && $stable(B)) |-> (X == A)
    );

endmodule