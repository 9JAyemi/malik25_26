module top_module_sva (
    input logic [99:0] in,
    input logic a,
    input logic b,
    input logic out_nor,
    input logic out_or,
    input logic out_xor
);
    ///// Combinational correctness (sampled on posedge of 'a') /////
    // out_or equals reduction OR of in.
    check_out_or_reduction: assert property (
        @(posedge a) out_or == (|in)
    );
    // out_xor equals reduction XOR of in.
    check_out_xor_reduction: assert property (
        @(posedge a) out_xor == (^in)
    );
    // out_nor equals reduction AND of in (by RTL composition).
    check_out_nor_is_and: assert property (
        @(posedge a) out_nor == (&in)
    );

    ///// Logical relationships implied by reductions /////
    // If out_nor is 1 (all bits are 1), out_or must be 1.
    check_nor_implies_or: assert property (
        @(posedge a) out_nor |-> out_or
    );
    // If out_or is 0 (all bits are 0), out_xor must be 0.
    check_or_zero_implies_xor_zero: assert property (
        @(posedge a) !out_or |-> (out_xor == 1'b0)
    );
    // If out_or is 0 (all bits are 0), out_nor must be 0.
    check_or_zero_implies_nor_zero: assert property (
        @(posedge a) !out_or |-> (out_nor == 1'b0)
    );
    // If out_xor is 1 (odd parity), out_or must be 1.
    check_xor_one_implies_or_one: assert property (
        @(posedge a) out_xor |-> out_or
    );
    // If out_nor is 1 (all ones, even count of ones), out_xor must be 0.
    check_nor_one_implies_xor_zero: assert property (
        @(posedge a) out_nor |-> (out_xor == 1'b0)
    );

    ///// Corner-case input patterns /////
    // When in is all zeros, all outputs are zero.
    check_all_zero_input: assert property (
        @(posedge a) (in == 100'b0) |-> (out_or == 1'b0 && out_xor == 1'b0 && out_nor == 1'b0)
    );
    // When in is all ones, out_or=1, out_xor=0 (even parity), out_nor=1.
    check_all_ones_input: assert property (
        @(posedge a) (in == {100{1'b1}}) |-> (out_or == 1'b1 && out_xor == 1'b0 && out_nor == 1'b1)
    );
endmodule