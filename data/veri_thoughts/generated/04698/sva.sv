module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

    // Output must match the XOR of the inputs.
    check_xor_equivalence: assert property (
        @(posedge clk) out == (a ^ b)
    );

    // Output must match the implemented sum-of-products form.
    check_sop_equivalence: assert property (
        @(posedge clk) out == ((a & ~b) | (~a & b))
    );

    // Equal inputs must drive the output low.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk) (a == b) |-> (out == 1'b0)
    );

    // Different inputs must drive the output high.
    check_different_inputs_drive_one: assert property (
        @(posedge clk) (a != b) |-> (out == 1'b1)
    );

    // 00 input case must produce 0.
    check_zero_zero_case: assert property (
        @(posedge clk) (!a && !b) |-> (out == 1'b0)
    );

    // 01 input case must produce 1.
    check_zero_one_case: assert property (
        @(posedge clk) (!a && b) |-> (out == 1'b1)
    );

    // 10 input case must produce 1.
    check_one_zero_case: assert property (
        @(posedge clk) (a && !b) |-> (out == 1'b1)
    );

    // 11 input case must produce 0.
    check_one_one_case: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b0)
    );

endmodule