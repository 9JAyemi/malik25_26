module functional_module_sva (
    input logic clk,            // External sampling clock (RTL is purely combinational)
    input logic a, b, c_in,
    input logic [3:0] in,
    input logic c_out,
    input logic sum,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);
    // sum must be XOR of a, b, c_in per full_adder.
    check_sum_is_xor: assert property (
        @(posedge clk) disable iff (1'b0) sum == (a ^ b ^ c_in)
    );

    // out_and is the AND of all in bits.
    check_out_and_def: assert property (
        @(posedge clk) disable iff (1'b0) out_and == (&in)
    );

    // out_or is the OR of all in bits.
    check_out_or_def: assert property (
        @(posedge clk) disable iff (1'b0) out_or == (|in)
    );

    // out_xor is the XOR of all in bits.
    check_out_xor_def: assert property (
        @(posedge clk) disable iff (1'b0) out_xor == (^in)
    );

    // c_out equals muxed carry: 0 when (sum & out_xor), else full_adder carry.
    check_cout_muxing: assert property (
        @(posedge clk) disable iff (1'b0)
            c_out == ( (sum & out_xor) ? 1'b0 : ((a & b) | (a & c_in) | (b & c_in)) )
    );

    // When (sum & out_xor) is true, c_out must be 0.
    check_cout_forced_low: assert property (
        @(posedge clk) disable iff (1'b0)
            (sum & out_xor) |-> (c_out == 1'b0)
    );

    // When (sum & out_xor) is false, c_out equals the full_adder carry.
    check_cout_equals_carry_when_not_forced: assert property (
        @(posedge clk) disable iff (1'b0)
            !(sum & out_xor) |-> (c_out == ((a & b) | (a & c_in) | (b & c_in)))
    );

    // If out_and is 1 (all inputs are 1), out_or must be 1.
    check_and_implies_or: assert property (
        @(posedge clk) disable iff (1'b0) out_and |-> out_or
    );

    // If out_or is 0, all inputs must be 0.
    check_or_zero_means_all_zero: assert property (
        @(posedge clk) disable iff (1'b0) (out_or == 1'b0) |-> (in == 4'b0000)
    );

    // If out_and is 1, all inputs must be 1.
    check_and_one_means_all_one: assert property (
        @(posedge clk) disable iff (1'b0) (out_and == 1'b1) |-> (in == 4'b1111)
    );

    // If all inputs are 1, parity over four ones is 0, so out_xor must be 0.
    check_and_implies_xor_zero: assert property (
        @(posedge clk) disable iff (1'b0) out_and |-> (out_xor == 1'b0)
    );
endmodule