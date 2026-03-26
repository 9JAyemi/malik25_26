module xor_module_sva(
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // data_out must equal data_in XOR 4'hF.
    check_data_out_xor_f: assert property (
        @($global_clock) data_out == (data_in ^ 4'hF)
    );

    // Bit 0 must be inverted from the input.
    check_bit0_inverted: assert property (
        @($global_clock) data_out[0] == ~data_in[0]
    );

    // Bit 1 must be inverted from the input.
    check_bit1_inverted: assert property (
        @($global_clock) data_out[1] == ~data_in[1]
    );

    // Bit 2 must be inverted from the input.
    check_bit2_inverted: assert property (
        @($global_clock) data_out[2] == ~data_in[2]
    );

    // Bit 3 must be inverted from the input.
    check_bit3_inverted: assert property (
        @($global_clock) data_out[3] == ~data_in[3]
    );

endmodule