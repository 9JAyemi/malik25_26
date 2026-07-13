module r_COMMAND_sva (
    input logic clk,
    input logic reset,       // active-high synchronous reset
    input logic wenb,        // active-low write enable
    input logic [7:0] in_data,
    input logic [7:0] reg_0x23
);
    // Reset drives reg_0x23 to 8'h00 on the next clock.
    check_reset_clears_reg_next: assert property (
        @(posedge clk) reset |-> (reg_0x23 == 8'h00)
    );

    // With wenb HIGH (no write), hold previous value to next cycle.
    check_hold_when_wenb_high: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b1) |-> (reg_0x23 == $past(reg_0x23))
    );

    // With wenb LOW, load in_data on the next cycle.
    check_update_on_wenb_low: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b0) |-> (reg_0x23 == $past(in_data))
    );

    // If the register changes and last cycle was not reset, last cycle must have had a write enable (wenb LOW).
    check_change_requires_prev_write_when_no_reset: assert property (
        @(posedge clk) disable iff (reset) ($changed(reg_0x23) && !$past(reset)) |-> ($past(wenb) == 1'b0)
    );

    // If last cycle was a write and in_data equaled the old value, the register must not change.
    check_write_same_value_no_change: assert property (
        @(posedge clk) disable iff (reset) ($past(wenb) == 1'b0 && ($past(in_data) == $past(reg_0x23))) |-> (reg_0x23 == $past(reg_0x23))
    );

    // If last cycle was a write and in_data differed from the old value, the register must change.
    check_write_diff_value_changes: assert property (
        @(posedge clk) disable iff (reset) ($past(wenb) == 1'b0 && ($past(in_data) != $past(reg_0x23))) |-> (reg_0x23 != $past(reg_0x23))
    );

    // Next-state relation when neither current nor previous cycle is in reset.
    check_next_state_definition: assert property (
        @(posedge clk) (!reset && !$past(reset)) |-> (reg_0x23 == (($past(wenb) == 1'b0) ? $past(in_data) : $past(reg_0x23)))
    );

    // Reset dominates write: if reset is asserted, next value is 0 regardless of wenb.
    check_reset_dominates_write: assert property (
        @(posedge clk) (reset && (wenb == 1'b0)) |-> (reg_0x23 == 8'h00)
    );
endmodule