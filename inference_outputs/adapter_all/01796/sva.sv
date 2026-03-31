module mem_encrypt_decrypt_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic [7:0] key,
    input logic enable,
    input logic [7:0] data_out
);
    // During reset, data_out must be 0.
    reset_clears_data_out: assert property (
        @(posedge clk) reset |-> (data_out == 8'h00)
    );

    // When enable is LOW, data_out equals data_in on the next cycle.
    pass_through_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (data_out == $past(data_in))
    );

    // When enable is HIGH, data_out equals data_in XOR key on the next cycle.
    encrypt_when_enabled: assert property (
        @(posedge clk) disable iff (reset) (enable) |=> (data_out == ($past(data_in) ^ $past(key)))
    );

    // If enable is HIGH and key is zero, data_out equals data_in on the next cycle.
    pass_through_when_key_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && (key == 8'h00)) |=> (data_out == $past(data_in))
    );

    // If enable is HIGH and data_in equals key, data_out equals zero on the next cycle.
    zero_when_data_equals_key: assert property (
        @(posedge clk) disable iff (reset) (enable && (data_in == key)) |=> (data_out == 8'h00)
    );

    // If enable is HIGH and data_in is zero, data_out equals key on the next cycle.
    key_when_data_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && (data_in == 8'h00)) |=> (data_out == $past(key))
    );

    // If enable is HIGH and key is all ones, data_out equals bitwise NOT of data_in on the next cycle.
    invert_when_key_all_ones: assert property (
        @(posedge clk) disable iff (reset) (enable && (key == 8'hFF)) |=> (data_out == ~$past(data_in))
    );

    // If enable is HIGH and data_in is all ones, data_out equals bitwise NOT of key on the next cycle.
    invert_key_when_data_all_ones: assert property (
        @(posedge clk) disable iff (reset) (enable && (data_in == 8'hFF)) |=> (data_out == ~$past(key))
    );

    // If enable is HIGH and key is all zeros, data_out equals bitwise NOT of data_in on the next cycle.
    invert_when_key_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && (key == 8'h00)) |=> (data_out == ~$past(data_in))
    );

    // If enable is HIGH and data_in equals bitwise NOT of key, data_out equals key on the next cycle.
    key_when_data_equals_not_key: assert property (
        @(posedge clk) disable iff (reset) (enable && (data_in == ~key)) |=> (data_out == $past(key))
    );
endmodule