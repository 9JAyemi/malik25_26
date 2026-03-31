module mem_enc_dec_sva (
    input logic clk,
    input logic [mem_width-1:0] mem_addr,
    input logic [mem_width-1:0] mem_data,
    input logic [key_width-1:0] key,
    input logic [mem_width-1:0] enc_data
);

// enc_data equals mem_data XOR key.
    check_encryption_function: assert property (
        @(posedge clk) enc_data == (mem_data ^ key)
    );

// XORing enc_data with key recovers mem_data.
    check_decryption_function: assert property (
        @(posedge clk) (enc_data ^ key) == mem_data
    );

// Equal operands XOR to zero.
    check_equal_operands_zero: assert property (
        @(posedge clk) (mem_data == key) |-> (enc_data == 8'h00)
    );

// Zero key passes mem_data through.
    check_zero_key_passthrough: assert property (
        @(posedge clk) (key == 8'h00) |-> (enc_data == mem_data)
    );

// Zero data passes key through.
    check_zero_data_passthrough: assert property (
        @(posedge clk) (mem_data == 8'h00) |-> (enc_data == key)
    );

endmodule
