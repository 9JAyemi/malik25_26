module gray_shift_register_sva (
    input logic CLK,
    input logic RST,
    input logic [7:0] data_in,
    input logic shift,
    input logic load,
    input logic select,
    input logic [7:0] shift_reg_out,
    input logic [7:0] counter_out,
    input logic [7:0] final_output
);

    // Reset clears the counter and shift register outputs.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) RST |-> ((counter_out == 8'h00) && (shift_reg_out == 8'h00))
    );

    // Reset clears the final output select path.
    check_reset_clears_select_path: assert property (
        @(posedge CLK) RST |-> (final_output == 8'h00)
    );

    // Reset clears the final output counter path.
    check_reset_clears_counter_path: assert property (
        @(posedge CLK) RST |-> (final_output == 8'h00)
    );

    // The counter output is the Gray code of the Gray counter.
    check_counter_matches_gray_counter: assert property (
        @(posedge CLK) disable iff (RST)
        (counter_out == (gray_counter_out ^ (gray_counter_out >> 1)))
    );

    // The shift register output is the Gray code of the shift register.
    check_shift_reg_matches_gray_shift_reg: assert property (
        @(posedge CLK) disable iff (RST)
        (shift_reg_out == (shift_reg ^ (shift_reg >> 1)))
    );

    // The final output follows the selected Gray path.
    check_final_output_selects_gray_path: assert property (
        @(posedge CLK) disable iff (RST)
        (final_output == (select ? shift_reg_out : counter_out))
    );

    // Load captures data_in into the shift register.
    check_load_captures_shift_reg: assert property (
        @(posedge CLK) disable iff (RST)
        load |=> (shift_reg == $past(data_in))
    );

    // Shift moves the shift register left and inserts 0 into bit 0.
    check_shift_moves_shift_reg: assert property (
        @(posedge CLK) disable iff (RST)
        (!load && shift) |=> (shift_reg == {$past(shift_reg[6:0]), 1'b0})
    );

    // With neither load nor shift, the shift register holds its value.
    check_hold_shift_reg: assert property (
        @(posedge CLK) disable iff (RST)
        (!load && !shift) |=> (shift_reg == $past(shift_reg))
    );

    // The Gray counter increments by one on each clock.
    check_gray_counter_increments: assert property (
        @(posedge CLK) disable iff (RST)
        1'b1 |=> (gray_counter_out == ($past(gray_counter_out) + 8'h01))
    );

endmodule