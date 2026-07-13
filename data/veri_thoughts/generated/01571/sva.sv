module r_FAULT_STATUS_sva (
    input logic clk,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic [7:0] reg_0x1F
);
    // Synchronous reset sets reg_0x1F to zero on the next cycle.
    reset_sets_zero_next: assert property (
        @(posedge clk) reset |=> (reg_0x1F == 8'h00)
    );

    // Reset has priority over writes (wenb low) and still drives zero next cycle.
    reset_overrides_write: assert property (
        @(posedge clk) (reset && (wenb == 1'b0)) |=> (reg_0x1F == 8'h00)
    );

    // When not in reset and wenb is LOW, capture in_data on the next cycle.
    write_captures_in_data: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b0) |=> (reg_0x1F == $past(in_data))
    );

    // When not in reset and wenb is HIGH, hold previous value on the next cycle.
    hold_on_wenb_high: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b1) |=> (reg_0x1F == $past(reg_0x1F))
    );

    // While reset remains asserted across cycles, the register is zero.
    reset_while_asserted_holds_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (reg_0x1F == 8'h00)
    );

    // After a reset cycle, if no write occurs, the value remains zero.
    hold_zero_after_reset_if_no_write: assert property (
        @(posedge clk) (!reset && (wenb == 1'b1) && $past(reset)) |-> (reg_0x1F == 8'h00)
    );

    // Even if in_data toggles, with wenb HIGH the register does not update.
    no_update_when_wenb_high_despite_data_change: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b1 && $changed(in_data)) |=> (reg_0x1F == $past(reg_0x1F))
    );

    // With back-to-back cycles of wenb HIGH (no writes), the register stays stable.
    stable_across_back_to_back_no_write: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b1 && $past(wenb) == 1'b1) |-> (reg_0x1F == $past(reg_0x1F))
    );

    // On a write with data different from the current value, the register must change next cycle.
    write_with_different_data_changes_reg: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b0 && (in_data != reg_0x1F)) |=> (reg_0x1F != $past(reg_0x1F))
    );
endmodule