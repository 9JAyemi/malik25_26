module r_TX_BUF_OBJ4_BYTE_1_sva (
    input logic clk,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic [7:0] reg_0x61
);

    ///// Reset behavior /////
    // While reset is asserted (active-high, synchronous), reg_0x61 is 0x00.
    check_reset_drives_zero: assert property (
        @(posedge clk) reset |-> (reg_0x61 == 8'h00)
    );

    ///// Functional update rules (active when not in reset) /////
    // On a write (wenb low) in the previous cycle, capture previous in_data.
    check_write_on_wenb_low: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(wenb) == 1'b0)) |-> (reg_0x61 == $past(in_data))
    );

    // On a hold (wenb high) in the previous cycle, retain the previous value.
    check_hold_on_wenb_high: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(wenb) == 1'b1)) |-> (reg_0x61 == $past(reg_0x61))
    );

    // Deterministic next-state function based on previous wenb.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (reg_0x61 == ($past(wenb) ? $past(reg_0x61) : $past(in_data)))
    );

    // If the value changed (and previous cycle was not in reset), the previous cycle must have been a write.
    check_change_implies_prev_write: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (reg_0x61 != $past(reg_0x61))) |-> ($past(wenb) == 1'b0)
    );

    // A write followed by a hold preserves the written value two cycles later.
    check_write_then_hold_preserves_value: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,2) && $past(!reset) && ($past(wenb,2) == 1'b0) && ($past(wenb) == 1'b1))
            |-> (reg_0x61 == $past(in_data,2))
    );

    // Back-to-back writes take the last cycle's in_data.
    check_back_to_back_writes_take_last: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,2) && $past(!reset) && ($past(wenb,2) == 1'b0) && ($past(wenb) == 1'b0))
            |-> (reg_0x61 == $past(in_data))
    );

    // First cycle after reset, if holding (wenb high), the register remains at 0x00.
    check_post_reset_hold_is_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) && (wenb == 1'b1)) |-> (reg_0x61 == 8'h00)
    );

    // Two consecutive holds (no reset in the past two cycles) keep the value from two cycles ago.
    check_two_consecutive_holds_stable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset,2) && $past(!reset) && ($past(wenb,2) == 1'b1) && ($past(wenb) == 1'b1))
            |-> (reg_0x61 == $past(reg_0x61,2))
    );

endmodule