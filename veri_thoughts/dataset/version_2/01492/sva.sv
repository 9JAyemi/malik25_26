module top_module_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C_in,
    input logic [8:0] out,
    input logic [1:0] fa1_out,
    input logic [1:0] fa2_out,
    input logic parity_bit
);
    // fa1 sum equals A ^ B ^ C_in.
    check_fa1_sum: assert property (
        @(posedge CLK) (fa1_out[0] == (A ^ B ^ C_in))
    );

    // fa1 carry equals (A & B) | (C_in & (A ^ B)).
    check_fa1_carry: assert property (
        @(posedge CLK) (fa1_out[1] == ((A & B) | (C_in & (A ^ B))))
    );

    // fa2 sum equals fa1_sum ^ fa1_carry ^ 1'b0.
    check_fa2_sum: assert property (
        @(posedge CLK) (fa2_out[0] == (fa1_out[0] ^ fa1_out[1] ^ 1'b0))
    );

    // fa2 carry equals (fa1_sum & fa1_carry) | (1'b0 & (fa1_sum ^ fa1_carry)).
    check_fa2_carry: assert property (
        @(posedge CLK) (fa2_out[1] == ((fa1_out[0] & fa1_out[1]) | (1'b0 & (fa1_out[0] ^ fa1_out[1]))))
    );

    // Parity bit equals (A ^ B ^ fa2_sum) & (A | B | fa2_sum).
    check_parity_definition: assert property (
        @(posedge CLK) (parity_bit == ((A ^ B ^ fa2_out[0]) & (A | B | fa2_out[0])))
    );

    // out[1:0] maps directly to fa2_out[1:0].
    check_out_lower_mapping: assert property (
        @(posedge CLK) (out[1:0] == fa2_out[1:0])
    );

    // out[2] maps directly to parity_bit.
    check_out_parity_mapping: assert property (
        @(posedge CLK) (out[2] == parity_bit)
    );

    // out[8:3] are zero due to width extension in assignment.
    check_out_upper_zero: assert property (
        @(posedge CLK) (out[8:3] == 6'b0)
    );

    // out[0] equals (A ^ B ^ C_in) ^ ((A & B) | (C_in & (A ^ B))).
    check_out0_from_inputs: assert property (
        @(posedge CLK) (out[0] == ((A ^ B ^ C_in) ^ ((A & B) | (C_in & (A ^ B)))))
    );

    // out[1] equals ((A ^ B ^ C_in) & ((A & B) | (C_in & (A ^ B)))).
    check_out1_from_inputs: assert property (
        @(posedge CLK) (out[1] == ((A ^ B ^ C_in) & ((A & B) | (C_in & (A ^ B)))))
    );
endmodule