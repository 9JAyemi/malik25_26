module combinational_circuit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);
    // Functional equivalence for out_and to pairwise AND then combine.
    check_out_and_truth: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_and == ((in[0] & in[1]) & (in[2] & in[3]))
    );

    // Functional equivalence for out_or to pairwise OR then combine.
    check_out_or_truth: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_or == ((in[0] | in[1]) | (in[2] | in[3]))
    );

    // Functional equivalence for out_xor to pairwise XOR then combine.
    check_out_xor_truth: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_xor == ((in[0] ^ in[1]) ^ (in[2] ^ in[3]))
    );

    // If all inputs are 1, out_and must be 1.
    check_all_ones_implies_and: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (&in) |-> (out_and == 1'b1)
    );

    // If out_and is 1, all inputs must be 1.
    check_and_implies_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_and |-> (&in)
    );

    // If out_or is 0, all inputs must be 0.
    check_or_zero_implies_all_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (out_or == 1'b0) |-> (~|in)
    );

    // If any input is 1, out_or must be 1.
    check_any_one_implies_or: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (|in) |-> (out_or == 1'b1)
    );

    // out_and being 1 implies out_or is 1.
    check_and_implies_or: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_and |-> (out_or == 1'b1)
    );

    // out_and being 1 implies out_xor is 0.
    check_and_implies_xor_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        out_and |-> (out_xor == 1'b0)
    );

    // All zeros on input force all outputs to expected zeros.
    check_all_zero_outputs_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (in == 4'b0000) |-> (out_and == 1'b0 && out_or == 1'b0 && out_xor == 1'b0)
    );
endmodule