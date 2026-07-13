module combinational_circuit_sva (
    input logic clk,
    input logic [3:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);
    // out_and equals the AND of all six pairwise input ANDs.
    check_out_and_matches_impl: assert property (
        @(posedge clk) out_and == ((in[0] & in[1]) & (in[0] & in[2]) & (in[0] & in[3]) & (in[1] & in[2]) & (in[1] & in[3]) & (in[2] & in[3]))
    );

    // out_or equals the OR of or1..or4 expression.
    check_out_or_matches_impl: assert property (
        @(posedge clk) out_or == (((in[0] | in[1]) | (in[0] | in[2])) | ((in[0] | in[3]) | (in[1] | in[2] | in[3])))
    );

    // out_xor equals the XOR chain of the three pairwise XORs with in[0].
    check_out_xor_matches_impl: assert property (
        @(posedge clk) out_xor == (((in[0] ^ in[1]) ^ (in[0] ^ in[2])) ^ (in[0] ^ in[3]))
    );

    // out_and equals reduction AND of all inputs.
    check_out_and_reduction: assert property (
        @(posedge clk) out_and == (&in)
    );

    // out_or equals reduction OR of all inputs.
    check_out_or_reduction: assert property (
        @(posedge clk) out_or == (|in)
    );

    // out_xor equals reduction XOR (parity) of all inputs.
    check_out_xor_reduction: assert property (
        @(posedge clk) out_xor == (^in)
    );

    // If out_and is 1 (all inputs 1), out_or must be 1 in the same cycle.
    check_out_and_implies_out_or: assert property (
        @(posedge clk) out_and |=> out_or
    );

    // If out_and is 1 (all inputs 1), out_xor must be 0 in the same cycle.
    check_out_and_implies_not_out_xor: assert property (
        @(posedge clk) out_and |=> (out_xor == 1'b0)
    );

    // If out_xor is 1 (odd parity), out_or must be 1 in the same cycle.
    check_out_xor_implies_out_or: assert property (
        @(posedge clk) out_xor |=> out_or
    );

    // If out_or is 0 (all inputs 0), then out_and and out_xor must both be 0.
    check_out_or_zero_forces_others_zero: assert property (
        @(posedge clk) (out_or == 1'b0) |=> ((out_and == 1'b0) && (out_xor == 1'b0))
    );
endmodule