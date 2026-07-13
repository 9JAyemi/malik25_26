module r_FAULT_STATUS_sva (
    input logic [7:0] reg_0x1F,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);

// Reset drives reg_0x1F to 0 on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (reg_0x1F == 8'h00)
    );

// Reset has priority over write enable when both are asserted.
    check_reset_priority_over_wenb: assert property (
        @(posedge clk) (reset && !wenb) |=> (reg_0x1F == 8'h00)
    );

// With wenb low, next value equals in_data.
    check_write_loads_data: assert property (
        @(posedge clk) disable iff (reset) (!wenb) |=> (reg_0x1F == $past(in_data))
    );

// With wenb high, next value holds its previous value.
    check_hold_when_wenb_high: assert property (
        @(posedge clk) disable iff (reset) wenb |=> (reg_0x1F == $past(reg_0x1F))
    );

endmodule
