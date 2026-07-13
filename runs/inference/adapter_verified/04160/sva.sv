module gray_shift_register_sva (
    input logic CLK,
    input logic RST,
    input logic [7:0] data_in,
    input logic shift,
    input logic load,
    input logic select,
    input logic [7:0] shift_reg_out,
    input logic [7:0] counter_out,
    input logic [7:0] final_output,
    input logic [7:0] gray_counter_out,
    input logic [7:0] shift_reg
);

// Reset clears both internal registers and outputs.
    check_reset_clears_registers: assert property (
        @(posedge CLK) RST |=> (gray_counter_out == 8'h00) && (shift_reg == 8'h00)
    );

// Counter increments by one on each non-reset cycle.
    check_counter_increments: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> (gray_counter_out == ($past(gray_counter_out) + 8'd1))
    );

// Counter wraps from 8'hFF to 8'h00.
    check_counter_wraps: assert property (
        @(posedge CLK) disable iff (RST) (gray_counter_out == 8'hFF) |=> (gray_counter_out == 8'h00)
    );

// Counter output matches the RTL XOR function.
    check_counter_output_function: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |-> (counter_out == (gray_counter_out ^ (gray_counter_out >> 1)))
    );

// Shift register loads data_in when load is asserted.
    check_shift_loads_data: assert property (
        @(posedge CLK) disable iff (RST) load |=> (shift_reg == $past(data_in))
    );

// Shift register shifts left by one when shift is asserted and load is not.
    check_shift_left: assert property (
        @(posedge CLK) disable iff (RST) (!load && shift) |=> (shift_reg == {$past(shift_reg[6:0]), 1'b0})
    );

// Shift register holds its value when neither load nor shift is asserted.
    check_shift_hold: assert property (
        @(posedge CLK) disable iff (RST) (!load && !shift) |=> (shift_reg == $past(shift_reg))
    );

// Shift register output matches the RTL XOR function.
    check_shift_output_function: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |-> (shift_reg_out == (shift_reg ^ (shift_reg >> 1)))
    );

// Final output selects counter output when select is high.
    check_final_output_selects_counter: assert property (
        @(posedge CLK) disable iff (RST) select |-> (final_output == counter_out)
    );

// Final output selects shift register output when select is low.
    check_final_output_selects_shift: assert property (
        @(posedge CLK) disable iff (RST) !select |-> (final_output == shift_reg_out)
    );

endmodule
