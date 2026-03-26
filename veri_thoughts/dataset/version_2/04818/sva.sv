module top_module_sva(
    input logic clk,
    input logic [15:0] in,
    input logic a,
    input logic b,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo,
    input logic [7:0] out_xor
);

    // Sampling clock only; the DUT is combinational and has no reset.

    // out_hi selects the upper byte when a^b is 0, else the lower byte.
    check_out_hi_function: assert property (
        @(posedge clk) out_hi == (((a ^ b) == 1'b0) ? in[15:8] : in[7:0])
    );

    // out_lo selects the lower byte when a^b is 0, else the upper byte.
    check_out_lo_function: assert property (
        @(posedge clk) out_lo == (((a ^ b) == 1'b0) ? in[7:0] : in[15:8])
    );

    // out_xor is always the XOR of the two split output bytes.
    check_out_xor_matches_outputs: assert property (
        @(posedge clk) out_xor == (out_hi ^ out_lo)
    );

    // out_xor equals the XOR of the original upper and lower input bytes.
    check_out_xor_matches_input_halves: assert property (
        @(posedge clk) out_xor == (in[15:8] ^ in[7:0])
    );

    // Equal control inputs keep the original byte order.
    check_equal_controls_keep_order: assert property (
        @(posedge clk) (a == b) |-> ({out_hi, out_lo} == in)
    );

    // Different control inputs swap the byte order.
    check_different_controls_swap_order: assert property (
        @(posedge clk) (a != b) |-> ({out_hi, out_lo} == {in[7:0], in[15:8]})
    );

    // Stable inputs keep all outputs stable across cycles.
    check_stable_inputs_preserve_outputs: assert property (
        @(posedge clk) $stable({in, a, b}) |-> $stable({out_hi, out_lo, out_xor})
    );

endmodule