module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic [1:0] in,
    input logic out_lut,
    input logic [1:0] out_and,
    input logic [1:0] out_or,
    input logic [1:0] out_xor,
    input logic final_output
);

    // External sampling clock; the RTL has no native clock or reset.

    // out_lut implements XOR of a and b.
    check_out_lut_is_xor: assert property (
        @(posedge clk) out_lut == (a ^ b)
    );

    // out_and matches the self-AND of in.
    check_out_and_self_and: assert property (
        @(posedge clk) out_and == (in & in)
    );

    // out_or matches the self-OR of in.
    check_out_or_self_or: assert property (
        @(posedge clk) out_or == (in | in)
    );

    // out_xor matches the self-XOR of in.
    check_out_xor_self_xor: assert property (
        @(posedge clk) out_xor == (in ^ in)
    );

    // final_output is the OR of all final_module inputs.
    check_final_output_or_of_sources: assert property (
        @(posedge clk) final_output == (out_lut | out_and[0] | out_and[1] | out_or[0] | out_or[1] | out_xor[0] | out_xor[1])
    );

    // The composed top-level function reduces to XOR(a,b) or either input bit.
    check_top_level_end_to_end_function: assert property (
        @(posedge clk) final_output == ((a ^ b) | in[0] | in[1])
    );

endmodule