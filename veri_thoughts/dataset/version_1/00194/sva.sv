module top_module_sva (
    input logic        clk,
    input logic [7:0]  in_hi,
    input logic [7:0]  in_lo,
    input logic [16:0] out
);

    // Upper output byte mirrors in_hi.
    check_hi_byte_mapping: assert property (
        @(posedge clk) out[16:9] == in_hi
    );

    // Lower output byte mirrors in_lo.
    check_lo_byte_mapping: assert property (
        @(posedge clk) out[8:1] == in_lo
    );

    // The upper 16 output bits are the concatenated input bytes.
    check_half_word_concat: assert property (
        @(posedge clk) out[16:1] == {in_hi, in_lo}
    );

    // The parity bit matches the reduction XOR of both input bytes.
    check_parity_from_inputs: assert property (
        @(posedge clk) out[0] == ^({in_hi, in_lo})
    );

    // The full output is the concatenated half-word with its parity bit.
    check_full_output_encoding: assert property (
        @(posedge clk) out == {in_hi, in_lo, ^({in_hi, in_lo})}
    );

    // The parity bit equals the parity of the upper 16 output bits.
    check_parity_consistency: assert property (
        @(posedge clk) out[0] == ^(out[16:1])
    );

    // The 17-bit output has even overall parity.
    check_even_output_parity: assert property (
        @(posedge clk) (^out) == 1'b0
    );

    // If both inputs are stable, the output remains stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({in_hi, in_lo}) |-> $stable(out)
    );

endmodule