module and_32_sva (
    input  logic        clk,
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [31:0] out
);
    // Output equals bitwise AND of a and b.
    check_out_equals_and: assert property (
        @(posedge clk) out == (a & b)
    );

    // Every 1 in out must also be 1 in a.
    check_out_subset_a: assert property (
        @(posedge clk) (out & ~a) == 32'b0
    );

    // Every 1 in out must also be 1 in b.
    check_out_subset_b: assert property (
        @(posedge clk) (out & ~b) == 32'b0
    );

    // If a is all zeros, out is all zeros.
    check_zero_a_implies_zero_out: assert property (
        @(posedge clk) (a == 32'b0) |-> (out == 32'b0)
    );

    // If b is all zeros, out is all zeros.
    check_zero_b_implies_zero_out: assert property (
        @(posedge clk) (b == 32'b0) |-> (out == 32'b0)
    );

    // If b is all ones, out equals a.
    check_b_all_ones_identity: assert property (
        @(posedge clk) (b == {32{1'b1}}) |-> (out == a)
    );

    // If a is all ones, out equals b.
    check_a_all_ones_identity: assert property (
        @(posedge clk) (a == {32{1'b1}}) |-> (out == b)
    );

    // If inputs are equal, out equals that value (idempotence).
    check_equal_inputs_idempotent: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // If any output bit is 1, both inputs have at least one 1.
    check_nonzero_out_implies_nonzero_inputs: assert property (
        @(posedge clk) (|out) |-> ((|a) && (|b))
    );

    // If both inputs are stable, output is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // Output changes only if at least one input changes.
    check_change_requires_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(a) || $changed(b))
    );
endmodule