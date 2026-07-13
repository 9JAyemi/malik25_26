module xor_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X
);
    // X implements XOR of A and B.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // When A is 0, X must equal B.
    check_A_zero_passthrough: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == B)
    );

    // When B is 0, X must equal A.
    check_B_zero_passthrough: assert property (
        @(posedge clk) (B == 1'b0) |-> (X == A)
    );

    // When A is 1, X must equal bitwise NOT of B.
    check_A_one_invert: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == ~B)
    );

    // When B is 1, X must equal bitwise NOT of A.
    check_B_one_invert: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == ~A)
    );

    // When A and B are equal, X must be 0.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (A == B) |-> (X == 1'b0)
    );

    // Output change parity equals XOR of input changes.
    check_toggle_parity: assert property (
        @(posedge clk) $changed(X) == ($changed(A) ^ $changed(B))
    );

    // If both inputs hold their values, X must also hold.
    check_hold_stability: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(X)
    );

    // If only A changes (B stable), X must change.
    check_toggle_with_A: assert property (
        @(posedge clk) ($changed(A) && $stable(B)) |-> $changed(X)
    );

    // If only B changes (A stable), X must change.
    check_toggle_with_B: assert property (
        @(posedge clk) ($changed(B) && $stable(A)) |-> $changed(X)
    );
endmodule