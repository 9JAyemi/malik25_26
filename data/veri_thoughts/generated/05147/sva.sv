module AOI_OR_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Z
);

    // No reset in the RTL; sample the combinational function on clk.

    // The AOI network implements XOR of A and B.
    check_output_matches_xor: assert property (
        @(posedge clk) Z == (A ^ B)
    );

    // Equal inputs must drive the output low.
    check_output_low_when_inputs_equal: assert property (
        @(posedge clk) (A == B) |-> (Z == 1'b0)
    );

    // Different inputs must drive the output high.
    check_output_high_when_inputs_differ: assert property (
        @(posedge clk) (A != B) |-> (Z == 1'b1)
    );

endmodule