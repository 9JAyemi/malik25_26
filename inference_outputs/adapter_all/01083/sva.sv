module adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum
);

    // sum must equal the 8-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == ({1'b0, A} + {1'b0, B})
    );

    // The least-significant sum bit must be the XOR of the input LSBs.
    check_sum_lsb_matches_input_lsbs: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0])
    );

    // Adding zero on B must pass A through with zero carry-out.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 8'h00) |-> (sum == {1'b0, A})
    );

    // Adding zero on A must pass B through with zero carry-out.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 8'h00) |-> (sum == {1'b0, B})
    );

    // The maximum input pair must produce 0xFF with carry-out.
    check_max_plus_max: assert property (
        @($global_clock) ((A == 8'hFF) && (B == 8'hFF)) |-> (sum == 9'h1FE)
    );

endmodule