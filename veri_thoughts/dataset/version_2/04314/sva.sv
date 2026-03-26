module top_module_sva (
    input logic [2:0] in_vec,
    input logic [2:0] out_vec,
    input logic [2:0] out_vec_int
);

    // Internal bit 0 is XOR of input bits 0 and 1.
    check_internal_bit0_xor: assert property (
        @($global_clock) out_vec_int[0] == (in_vec[0] ^ in_vec[1])
    );

    // Internal bit 1 is XOR of input bits 1 and 2.
    check_internal_bit1_xor: assert property (
        @($global_clock) out_vec_int[1] == (in_vec[1] ^ in_vec[2])
    );

    // Internal bit 2 passes through input bit 2.
    check_internal_bit2_passthrough: assert property (
        @($global_clock) out_vec_int[2] == in_vec[2]
    );

    // Top output is the internal vector XORed with constant 3'b010.
    check_output_mask_xor: assert property (
        @($global_clock) ((out_vec ^ out_vec_int) == 3'b010)
    );

    // End-to-end output matches the implemented mapping.
    check_end_to_end_mapping: assert property (
        @($global_clock) out_vec == {in_vec[2], (in_vec[1] ~^ in_vec[2]), (in_vec[0] ^ in_vec[1])}
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .in_vec(in_vec),
    .out_vec(out_vec),
    .out_vec_int(out_vec_int)
);