module register_counter_xor_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] reg_data_in,
    input logic reg_load,
    input logic counter_enable,
    input logic [7:0] output_data,

    // Internal signals from RTL (bind hierarchically)
    input logic [3:0] register_data,
    input logic [3:0] counter_data
);
    // Asserting reset drives register and counter to 0 and output to 0xFF.
    reset_state: assert property (
        @(posedge clk) (!reset) |-> (register_data == 4'b0000) && (counter_data == 4'b0000) && (output_data == 8'hFF)
    );

    // Register loads reg_data_in on next cycle when reg_load is high.
    check_register_load: assert property (
        @(posedge clk) disable iff (!reset) reg_load |=> (register_data == $past(reg_data_in))
    );

    // Register holds its value when reg_load is low.
    check_register_hold: assert property (
        @(posedge clk) disable iff (!reset) !reg_load |=> (register_data == $past(register_data))
    );

    // Counter increments by 1 on next cycle when counter_enable is high.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (!reset) counter_enable |=> (counter_data == $past(counter_data) + 4'd1)
    );

    // Counter holds its value when counter_enable is low.
    check_counter_hold: assert property (
        @(posedge clk) disable iff (!reset) !counter_enable |=> (counter_data == $past(counter_data))
    );

    // Output is XOR of concatenated register and counter with 0xFF.
    check_output_is_xor: assert property (
        @(posedge clk) disable iff (!reset) output_data == ({register_data, counter_data} ^ 8'hFF)
    );

    // Upper nibble of output equals register_data XOR 0xF.
    check_output_upper_nibble: assert property (
        @(posedge clk) disable iff (!reset) output_data[7:4] == (register_data ^ 4'hF)
    );

    // Lower nibble of output equals counter_data XOR 0xF.
    check_output_lower_nibble: assert property (
        @(posedge clk) disable iff (!reset) output_data[3:0] == (counter_data ^ 4'hF)
    );

    // Next-cycle output when only reg_load is asserted.
    check_output_next_reg_load_only: assert property (
        @(posedge clk) disable iff (!reset)
            (reg_load && !counter_enable) |=> (output_data == ({$past(reg_data_in), $past(counter_data)} ^ 8'hFF))
    );

    // Next-cycle output when only counter_enable is asserted.
    check_output_next_counter_only: assert property (
        @(posedge clk) disable iff (!reset)
            (!reg_load && counter_enable) |=> (output_data == ({$past(register_data), ($past(counter_data) + 4'd1)} ^ 8'hFF))
    );

    // Next-cycle output when both reg_load and counter_enable are asserted.
    check_output_next_both: assert property (
        @(posedge clk) disable iff (!reset)
            (reg_load && counter_enable) |=> (output_data == ({$past(reg_data_in), ($past(counter_data) + 4'd1)} ^ 8'hFF))
    );

    // Output holds when neither reg_load nor counter_enable are asserted.
    check_output_hold_when_idle: assert property (
        @(posedge clk) disable iff (!reset) (!reg_load && !counter_enable) |=> (output_data == $past(output_data))
    );
endmodule