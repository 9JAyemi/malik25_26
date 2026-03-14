module shift_register_adder_sva (
    input  logic [49:0] in,
    input  logic        out_and,
    input  logic        out_or,
    input  logic        out_xor,
    input  logic [1:0]  shift,
    input  logic [15:0] sum_output
);
    // Combinational DUT; no clock/reset in RTL. Sample SVA on posedge of in[0].
    // out_* are functions of (in << shift)[49:48]; sum_output is low 16 bits of ((in << shift) + out_xor).

    // out_and equals AND of top two adjacent bits of (in << shift).
    check_out_and_def: assert property (
        @(posedge in[0]) out_and == ((in << shift)[48] & (in << shift)[49])
    );

    // out_or equals OR of top two adjacent bits of (in << shift).
    check_out_or_def: assert property (
        @(posedge in[0]) out_or == ((in << shift)[48] | (in << shift)[49])
    );

    // out_xor equals XOR of top two adjacent bits of (in << shift).
    check_out_xor_def: assert property (
        @(posedge in[0]) out_xor == ((in << shift)[48] ^ (in << shift)[49])
    );

    // sum_output equals low 16 bits of ((in << shift) + out_xor).
    check_sum_output_def: assert property (
        @(posedge in[0]) sum_output == (((in << shift) + out_xor)[15:0])
    );

    // If out_xor is 0, sum_output equals low 16 bits of (in << shift).
    check_sum_when_outxor0: assert property (
        @(posedge in[0]) (out_xor == 1'b0) |-> (sum_output == (in << shift)[15:0])
    );

    // If out_xor is 1, sum_output equals low 16 bits of ((in << shift)[15:0] + 1).
    check_sum_when_outxor1: assert property (
        @(posedge in[0]) (out_xor == 1'b1) |-> (sum_output == (((in << shift)[15:0] + 16'd1)[15:0]))
    );

    // LSB of sum_output equals LSB of (in << shift) XOR out_xor.
    check_sum_bit0: assert property (
        @(posedge in[0]) sum_output[0] == ((in << shift)[0] ^ out_xor)
    );

    // Boolean consistency: OR equals AND OR XOR for same two bits.
    check_or_consistency: assert property (
        @(posedge in[0]) out_or == (out_and | out_xor)
    );

    // Boolean consistency: XOR equals OR XOR AND.
    check_xor_consistency: assert property (
        @(posedge in[0]) out_xor == (out_or ^ out_and)
    );

    // Boolean consistency: AND equals OR AND NOT(XOR).
    check_and_consistency: assert property (
        @(posedge in[0]) out_and == (out_or & ~out_xor)
    );

    // If AND is 1 then OR must be 1.
    check_and_implies_or: assert property (
        @(posedge in[0]) out_and |-> out_or
    );

    // If OR is 0 then AND and XOR must be 0.
    check_or_zero_implies_others_zero: assert property (
        @(posedge in[0]) (out_or == 1'b0) |-> ((out_and == 1'b0) && (out_xor == 1'b0))
    );

    // If AND is 1 then XOR must be 0.
    check_and_implies_not_xor: assert property (
        @(posedge in[0]) out_and |-> (out_xor == 1'b0)
    );

endmodule