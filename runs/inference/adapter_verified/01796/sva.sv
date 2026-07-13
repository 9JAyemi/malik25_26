module mem_encrypt_decrypt_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic [7:0] key,
    input logic enable,
    input logic [7:0] data_out
);

// Reset clears the output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (data_out == 8'h00)
    );

// With enable high, the next output is the current input XOR key.
    check_encrypt_on_enable: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (data_out == ($past(data_in) ^ $past(key)))
    );

// With enable low, the next output passes the current input through.
    check_passthrough_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (data_out == $past(data_in))
    );

// When enabled with zero key, the next output equals the current input.
    check_zero_key_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (key == 8'h00)) |=> (data_out == $past(data_in))
    );

// When enabled with zero input, the next output equals the key.
    check_zero_input_uses_key: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (data_in == 8'h00)) |=> (data_out == $past(key))
    );

// When enabled with the same input and key, the next output is zero.
    check_self_xor_zero: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (data_in == key)) |=> (data_out == 8'h00)
    );

endmodule
