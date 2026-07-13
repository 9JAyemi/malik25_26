module top_module_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic en,
    input logic [3:0] data_in,
    input logic [3:0] counter_out,
    input logic [3:0] gray_out,
    input logic [3:0] final_output
);

    // Load transfers data_in into the counter on the next clock.
    check_load_updates_counter: assert property (
        @(posedge clk) en && load |=> counter_out == $past(data_in)
    );

    // Disabled counter holds its value.
    check_hold_counter_when_disabled: assert property (
        @(posedge clk) !en |=> counter_out == $past(counter_out)
    );

    // Enabled counter increments when load is low and up_down is high.
    check_increment_counter: assert property (
        @(posedge clk) en && !load && up_down |=> counter_out == ($past(counter_out) + 4'd1)
    );

    // Enabled counter decrements when load is low and up_down is low.
    check_decrement_counter: assert property (
        @(posedge clk) en && !load && !up_down |=> counter_out == ($past(counter_out) - 4'd1)
    );

    // Gray output matches the binary-to-gray conversion of the counter.
    check_gray_encoding: assert property (
        @(posedge clk) gray_out == {counter_out[3], counter_out[3] ^ counter_out[2], counter_out[2] ^ counter_out[1], counter_out[1] ^ counter_out[0]}
    );

    // Final output is the XOR of counter and gray outputs.
    check_final_output_xor: assert property (
        @(posedge clk) final_output == (counter_out ^ gray_out)
    );

    // Final output equals the counter shifted right by one with zero fill.
    check_final_output_shift_relation: assert property (
        @(posedge clk) final_output == {1'b0, counter_out[3:1]}
    );

    // Loading data produces the corresponding gray code on the next cycle.
    check_load_updates_gray: assert property (
        @(posedge clk) en && load |=> gray_out == {$past(data_in[3]), $past(data_in[3]) ^ $past(data_in[2]), $past(data_in[2]) ^ $past(data_in[1]), $past(data_in[1]) ^ $past(data_in[0])}
    );

    // Loading data produces the corresponding final output on the next cycle.
    check_load_updates_final_output: assert property (
        @(posedge clk) en && load |=> final_output == {1'b0, $past(data_in[3:1])}
    );

    // Derived outputs stay stable when the counter is disabled.
    check_outputs_hold_when_disabled: assert property (
        @(posedge clk) !en |=> $stable(gray_out) && $stable(final_output)
    );

endmodule