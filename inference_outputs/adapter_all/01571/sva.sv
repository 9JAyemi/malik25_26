module r_FAULT_STATUS_sva (
    input logic [7:0] reg_0x1F,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);
    // Reset drives reg_0x1F to 0x00 on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (reg_0x1F == 8'h00)
    );

    // When not in reset and wenb is 0, next value equals in_data.
    write_updates_value: assert property (
        @(posedge clk) disable iff (reset) (!wenb) |=> (reg_0x1F == $past(in_data))
    );

    // When not in reset and wenb is 1, next value holds its previous value.
    hold_when_wenb_high: assert property (
        @(posedge clk) disable iff (reset) (wenb) |=> (reg_0x1F == $past(reg_0x1F))
    );

    // Any change in reg_0x1F must be caused by reset or a prior write (wenb==0).
    change_requires_reset_or_write: assert property (
        @(posedge clk) disable iff (reset) (reg_0x1F != $past(reg_0x1F)) |-> ($past(reset) || !$past(wenb))
    );

    // If reset is held high across cycles, reg_0x1F is 0x00 in the later cycle.
    reset_hold_keeps_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (reg_0x1F == 8'h00)
    );

    // If reset is held high across cycles, reg_0x1F remains stable.
    reset_hold_keeps_stable: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (reg_0x1F == $past(reg_0x1F))
    );

    // If not in reset and wenb is 0, reg_0x1F changes to the prior in_data.
    write_changes_value: assert property (
        @(posedge clk) disable iff (reset) (!wenb) |=> (reg_0x1F != $past(reg_0x1F))
    );

    // If not in reset and wenb is 1, reg_0x1F does not change.
    hold_no_change: assert property (
        @(posedge clk) disable iff (reset) (wenb) |=> (reg_0x1F == $past(reg_0x1F))
    );

    // If not in reset and wenb is 0, the new value equals the prior in_data.
    write_updates_to_prior_in: assert property (
        @(posedge clk) disable iff (reset) (!wenb) |=> (reg_0x1F == $past(in_data))
    );

    // If not in reset and wenb is 1, the new value equals the prior reg_0x1F.
    hold_updates_to_prior_reg: assert property (
        @(posedge clk) disable iff (reset) (wenb) |=> (reg_0x1F == $past(reg_0x1F))
    );
endmodule