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

    // Reset clears the gray counter on the next clock.
    check_gray_counter_reset: assert property (
        @(posedge CLK) RST |=> (gray_counter_out == 8'h00)
    );

    // Reset clears the shift register on the next clock.
    check_shift_reg_reset: assert property (
        @(posedge CLK) RST |=> (shift_reg == 8'h00)
    );

    // The gray counter increments by one when not in reset.
    check_gray_counter_increment: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> (gray_counter_out == ($past(gray_counter_out) + 8'h01))
    );

    // Load captures data_in into the shift register.
    check_shift_reg_load: assert property (
        @(posedge CLK) disable iff (RST) load |=> (shift_reg == $past(data_in))
    );

    // Shift moves the previous shift register value left and inserts zero.
    check_shift_reg_shift: assert property (
        @(posedge CLK) disable iff (RST) (!load && shift) |=> (shift_reg == {$past(shift_reg[6:0]), 1'b0})
    );

    // Without load or shift, the shift register holds its value.
    check_shift_reg_hold: assert property (
        @(posedge CLK) disable iff (RST) (!load && !shift) |=> (shift_reg == $past(shift_reg))
    );

    // counter_out is the XOR of gray_counter_out and its right shift.
    check_counter_out_definition: assert property (
        @(posedge CLK) disable iff (RST) counter_out == (gray_counter_out ^ (gray_counter_out >> 1))
    );

    // shift_reg_out is the XOR of shift_reg and its right shift.
    check_shift_reg_out_definition: assert property (
        @(posedge CLK) disable iff (RST) shift_reg_out == (shift_reg ^ (shift_reg >> 1))
    );

    // final_output selects counter_out when select is low.
    check_final_output_counter_path: assert property (
        @(posedge CLK) disable iff (RST) (!select) |-> (final_output == counter_out)
    );

    // final_output selects shift_reg_out when select is high.
    check_final_output_shift_path: assert property (
        @(posedge CLK) disable iff (RST) select |-> (final_output == shift_reg_out)
    );

endmodule