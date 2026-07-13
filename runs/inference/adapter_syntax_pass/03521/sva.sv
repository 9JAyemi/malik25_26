module mem_enc_dec_sva #(
    parameter int mem_width = 8,
    parameter int key_width = 8
) (
    input logic [mem_width-1:0] mem_addr,
    input logic [mem_width-1:0] mem_data,
    input logic [key_width-1:0] key,
    input logic [mem_width-1:0] enc_data
);

    // enc_data must equal mem_data XOR key.
    check_enc_data_matches_xor: assert property (
        @($global_clock) enc_data == (mem_data ^ key)
    );

    // A zero key must pass mem_data through unchanged.
    check_zero_key_passthrough: assert property (
        @($global_clock) (key == {key_width{1'b0}}) |-> (enc_data == mem_data)
    );

    // A zero data input must produce a zero output.
    check_zero_data_zero_output: assert property (
        @($global_clock) (mem_data == {mem_width{1'b0}}) |-> (enc_data == {mem_width{1'b0}})
    );

    // Equal mem_data and key must produce a zero output.
    check_equal_data_and_key_zero_output: assert property (
        @($global_clock) (mem_data == key) |-> (enc_data == {mem_width{1'b0}})
    );

    // Equal mem_data and key must also produce equal mem_addr and enc_data.
    check_equal_data_and_key_equal_addr_and_enc: assert property (
        @($global_clock) (mem_data == key) |-> (mem_addr == enc_data)
    );

    // A zero output must imply equal mem_data and key.
    check_zero_output_implies_equal_data_and_key: assert property (
        @($global_clock) (enc_data == {mem_width{1'b0}}) |-> (mem_data == key)
    );

endmodule