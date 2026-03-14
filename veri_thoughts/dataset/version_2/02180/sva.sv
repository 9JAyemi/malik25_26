module top_module_sva (
    input logic CLK,
    input logic [99:0] in1,
    input logic [99:0] in2,
    input logic [99:0] out_xor,
    input logic [99:0] out_and,
    input logic [199:0] out_func
);
    // No clock/reset in RTL; purely combinational. Sample checks on CLK.

    // out_xor equals bitwise XOR of inputs.
    check_out_xor_def: assert property (
        @(posedge CLK) out_xor == (in1 ^ in2)
    );

    // out_and equals bitwise AND of inputs.
    check_out_and_def: assert property (
        @(posedge CLK) out_and == (in1 & in2)
    );

    // out_func concatenates out_xor (MSBs) and out_and (LSBs).
    check_out_func_concat_outputs: assert property (
        @(posedge CLK) out_func == {out_xor, out_and}
    );

    // Upper half of out_func matches out_xor.
    check_out_func_upper_equals_out_xor: assert property (
        @(posedge CLK) out_func[199:100] == out_xor
    );

    // Lower half of out_func matches out_and.
    check_out_func_lower_equals_out_and: assert property (
        @(posedge CLK) out_func[99:0] == out_and
    );

    // out_func equals direct concat of computed XOR and AND from inputs.
    check_out_func_direct_from_inputs: assert property (
        @(posedge CLK) out_func == {in1 ^ in2, in1 & in2}
    );

    // XOR and AND results are never 1 on the same bit.
    check_xor_and_mutex: assert property (
        @(posedge CLK) (out_xor & out_and) == '0
    );

    // Bitwise OR of XOR and AND equals bitwise OR of inputs.
    check_or_relation: assert property (
        @(posedge CLK) (out_xor | out_and) == (in1 | in2)
    );

    // When inputs are equal, XOR is zero and AND equals that value.
    check_equal_inputs_behavior: assert property (
        @(posedge CLK) (in1 == in2) |-> (out_xor == '0) && (out_and == in1)
    );

    // When in1 is zero, XOR equals in2 and AND is zero.
    check_zero_in1_behavior: assert property (
        @(posedge CLK) (in1 == '0) |-> (out_xor == in2) && (out_and == '0)
    );
endmodule