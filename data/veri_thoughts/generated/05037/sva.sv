module top_module_sva (
    input logic clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [8:0] out,
    input logic [7:0] sum
);

    // Combinational RTL with no native clock or reset; sample on an external clock.

    // out[7:0] is the bitwise XOR of the two inputs.
    check_out_low_is_xor: assert property (
        @(posedge clk) out[7:0] == (in1 ^ in2)
    );

    // out[8] is the parity of the XOR result.
    check_out_msb_is_input_parity: assert property (
        @(posedge clk) out[8] == (^(in1 ^ in2))
    );

    // out[8] matches the parity of out[7:0].
    check_out_msb_matches_out_low_parity: assert property (
        @(posedge clk) out[8] == (^out[7:0])
    );

    // out concatenates the parity bit with the XOR result.
    check_out_concatenation: assert property (
        @(posedge clk) out == { (^(in1 ^ in2)), (in1 ^ in2) }
    );

    // sum equals in1 plus in2 plus the connected out[8] bit.
    check_sum_uses_out_msb: assert property (
        @(posedge clk) sum == (in1 + in2 + out[8])
    );

    // sum equals in1 plus in2 plus parity of the XOR result.
    check_sum_matches_input_parity: assert property (
        @(posedge clk) sum == (in1 + in2 + (^(in1 ^ in2)))
    );

endmodule