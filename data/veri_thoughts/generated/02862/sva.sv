module data_register_sva (
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk,
    input logic [7:0] out_data
);
    // Clock: clk. Reset: reset active-low (asynchronous). Sequential 8-bit register with write enable; hold otherwise.

    // While reset is asserted LOW, out_data must be 0x00.
    check_in_reset_forces_zero: assert property (
        @(posedge clk) (!reset) |-> (out_data == 8'h00)
    );

    // On the cycle after reset was LOW, out_data is still 0x00.
    check_post_reset_zero: assert property (
        @(posedge clk) $past(!reset) |-> (out_data == 8'h00)
    );

    // First cycle after deasserting reset with no write, out_data remains 0x00.
    check_deassert_no_write_keeps_zero: assert property (
        @(posedge clk) disable iff (!reset) ($past(!reset) && reset && !wenb) |-> (out_data == 8'h00)
    );

    // First cycle after deasserting reset with a write, next cycle out_data equals in_data of the deassert cycle.
    check_deassert_write_updates_next: assert property (
        @(posedge clk) disable iff (!reset) ($past(!reset) && reset && wenb) |-> ##1 (out_data == $past(in_data))
    );

    // With reset HIGH in consecutive cycles, a write in the previous cycle updates out_data with previous in_data.
    check_write_updates_from_prev_cycle: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && $past(wenb)) |-> (out_data == $past(in_data))
    );

    // With reset HIGH in consecutive cycles, no write in the previous cycle holds out_data stable.
    check_hold_when_no_write: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && !$past(wenb)) |-> (out_data == $past(out_data))
    );

endmodule