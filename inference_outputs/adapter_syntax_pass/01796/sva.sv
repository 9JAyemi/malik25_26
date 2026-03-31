module mem_encrypt_decrypt_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic [7:0] key,
    input logic enable,
    input logic [7:0] data_out
);

    // Reset forces the output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |-> (data_out == 8'h00)
    );

    // When enabled, the next output is the previous cycle's data_in XOR key.
    check_enabled_updates_output: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (data_out == ($past(data_in) ^ $past(key)))
    );

    // When disabled, the next output is the previous cycle's data_in.
    check_disabled_passes_input: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (data_out == $past(data_in))
    );

    // The output always matches the previous cycle's selected behavior.
    check_output_matches_previous_cycle: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (data_out == ($past(enable) ? ($past(data_in) ^ $past(key)) : $past(data_in)))
    );

endmodule