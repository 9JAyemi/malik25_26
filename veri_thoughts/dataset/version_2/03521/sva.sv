module mem_enc_dec_sva #(
    parameter mem_width = 8,
    parameter key_width = 8
) (
    input logic [mem_width-1:0] mem_addr,
    input logic [mem_width-1:0] mem_data,
    input logic [key_width-1:0] key,
    input logic [mem_width-1:0] enc_data
);

    // Purely combinational RTL; no explicit clock or reset, so assertions sample on $global_clock.

    // Encoded data always matches the RTL XOR assignment.
    check_encode_function: assert property (
        @($global_clock) enc_data == mem_width'(mem_data ^ key)
    );

    // Output stays stable when data and key stay stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(mem_data) && $stable(key)) |-> $stable(enc_data)
    );

    // Address changes alone do not affect the encoded output.
    check_addr_change_has_no_effect: assert property (
        @($global_clock) ($changed(mem_addr) && $stable(mem_data) && $stable(key)) |-> $stable(enc_data)
    );

    // With a stable key, output delta matches the data delta.
    check_output_delta_matches_data_delta_when_key_stable: assert property (
        @($global_clock) $stable(key) |-> ((enc_data ^ $past(enc_data)) == (mem_data ^ $past(mem_data)))
    );

    // With stable data, output delta matches the effective key delta.
    check_output_delta_matches_key_delta_when_data_stable: assert property (
        @($global_clock) $stable(mem_data) |-> ((enc_data ^ $past(enc_data)) == (mem_width'(key) ^ mem_width'($past(key))))
    );

endmodule