module mem_enc_dec_sva #(
    parameter int mem_width = 8,
    parameter int key_width = 8
) (
    input logic clk,
    input logic [mem_width-1:0] mem_addr,
    input logic [mem_width-1:0] mem_data,
    input logic [key_width-1:0] key,
    input logic [mem_width-1:0] enc_data
);

    // enc_data must equal mem_data XOR key.
    check_encryption_xor: assert property (
        @(posedge clk) enc_data == (mem_data ^ key)
    );

    // If mem_data is stable, enc_data must remain stable.
    check_enc_data_stable_when_mem_data_stable: assert property (
        @(posedge clk) $stable(mem_data) |-> $stable(enc_data)
    );

    // If key is stable, enc_data must remain stable.
    check_enc_data_stable_when_key_stable: assert property (
        @(posedge clk) $stable(key) |-> $stable(enc_data)
    );

    // If mem_data and key are stable, enc_data must remain stable.
    check_enc_data_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(mem_data) && $stable(key)) |-> $stable(enc_data)
    );

    // If enc_data changes, at least one of mem_data or key must have changed.
    check_enc_data_change_requires_input_change: assert property (
        @(posedge clk) $changed(enc_data) |-> ($changed(mem_data) || $changed(key))
    );

    // If mem_addr changes, enc_data must remain stable.
    check_enc_data_ignores_address: assert property (
        @(posedge clk) $changed(mem_addr) |-> $stable(enc_data)
    );

    // If key width is less than mem width, key is zero-extended before XOR.
    generate
        if (key_width < mem_width) begin : gen_key_zero_extend
            check_key_zero_extend: assert property (
                @(posedge clk) enc_data == (mem_data ^ {mem_width{key[0]}})
            );
        end
    endgenerate

    // If key width is greater than mem width, key is truncated before XOR.
    generate
        if (key_width > mem_width) begin : gen_key_truncate
            check_key_truncate: assert property (
                @(posedge clk) enc_data == (mem_data ^ key[key_width-1:0])
            );
        end
    endgenerate

endmodule