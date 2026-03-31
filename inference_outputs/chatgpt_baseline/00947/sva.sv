module top_module_sva (
    input logic CLK,
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);
    ///// Functional equivalence to reduction operators /////
    // out_and equals bitwise reduction AND of in.
    check_out_and_equals_reduction: assert property (
        @(posedge CLK) (out_and === (&in))
    );
    // out_or equals bitwise reduction OR of in.
    check_out_or_equals_reduction: assert property (
        @(posedge CLK) (out_or === (|in))
    );
    // out_xor equals bitwise reduction XOR (parity) of in.
    check_out_xor_equals_reduction: assert property (
        @(posedge CLK) (out_xor === (^in))
    );

    ///// Output relationships derived from logic /////
    // If all bits are 1 (out_and==1), then out_or must be 1.
    check_and_implies_or: assert property (
        @(posedge CLK) (out_and === 1'b1) |-> (out_or === 1'b1)
    );
    // If no bit is 1 (out_or==0), then out_and must be 0.
    check_or_zero_implies_and_zero: assert property (
        @(posedge CLK) (out_or === 1'b0) |-> (out_and === 1'b0)
    );
    // If no bit is 1 (out_or==0), parity must be 0.
    check_or_zero_implies_xor_zero: assert property (
        @(posedge CLK) (out_or === 1'b0) |-> (out_xor === 1'b0)
    );
    // If parity is 1, at least one bit is 1 (out_or==1).
    check_xor_one_implies_or_one: assert property (
        @(posedge CLK) (out_xor === 1'b1) |-> (out_or === 1'b1)
    );

    ///// Specific input patterns /////
    // For all-zeros input, all outputs are 0.
    check_all_zeros_input_outputs_zero: assert property (
        @(posedge CLK) (in === {100{1'b0}}) |-> ((out_and === 1'b0) && (out_or === 1'b0) && (out_xor === 1'b0))
    );
    // For all-ones input, out_and=1, out_or=1, out_xor=0 (100 is even).
    check_all_ones_input_outputs_expected: assert property (
        @(posedge CLK) (in === {100{1'b1}}) |-> ((out_and === 1'b1) && (out_or === 1'b1) && (out_xor === 1'b0))
    );
    // For exactly one bit set, out_or=1, out_and=0, out_xor=1.
    check_onehot_input_outputs_expected: assert property (
        @(posedge CLK) $onehot(in) |-> ((out_or === 1'b1) && (out_and === 1'b0) && (out_xor === 1'b1))
    );

    ///// Temporal sanity for combinational behavior /////
    // If input is unchanged, all outputs remain unchanged.
    check_outputs_stable_when_input_stable: assert property (
        @(posedge CLK) $stable(in) |-> ($stable(out_and) && $stable(out_or) && $stable(out_xor))
    );
    // If exactly one input bit toggles, parity output toggles.
    check_xor_toggles_on_single_bit_change: assert property (
        @(posedge CLK) $onehot(in ^ $past(in)) |-> (out_xor !== $past(out_xor))
    );
endmodule