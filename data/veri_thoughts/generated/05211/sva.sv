module pcie_reset_delay_v6_sva #(
    parameter string PL_FAST_TRAIN = "FALSE",
    parameter int REF_CLK_FREQ = 0,
    parameter int TCQ = 1
)(
    input logic       ref_clk,
    input logic       sys_reset_n,
    input logic       delayed_sys_reset_n,
    input logic [7:0] reg_count_7_0,
    input logic [7:0] reg_count_15_8,
    input logic [7:0] reg_count_23_16
);

    // Clock: ref_clk
    // Reset: sys_reset_n, active low
    // Logic: sequential counter with combinational output decode
    localparam int TBIT = (PL_FAST_TRAIN == "FALSE") ? ((REF_CLK_FREQ == 1) ? 20 : (REF_CLK_FREQ == 0) ? 20 : 21) : 2;

    wire [23:0] concat_count;
    assign concat_count = {reg_count_23_16, reg_count_15_8, reg_count_7_0};

    // Reset clears the counter and forces the delayed reset low.
    check_reset_clears_counter: assert property (
        @(posedge ref_clk)
        !sys_reset_n |-> (reg_count_7_0 == 8'h00) &&
                         (reg_count_15_8 == 8'h00) &&
                         (reg_count_23_16 == 8'h00) &&
                         (delayed_sys_reset_n == 1'b0)
    );

    // The output is always the selected counter bit.
    check_output_matches_selected_bit: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        delayed_sys_reset_n == concat_count[TBIT]
    );

    // The low byte increments every cycle while the delayed reset is low.
    check_low_byte_increments_while_output_low: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        !delayed_sys_reset_n |=> (reg_count_7_0 == ($past(reg_count_7_0) + 8'h01))
    );

    // The full 24-bit counter increments by one while the delayed reset is low.
    check_counter_increments_while_output_low: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        !delayed_sys_reset_n |=> (concat_count == ($past(concat_count) + 24'h000001))
    );

    // The counter stops changing once the delayed reset goes high.
    check_counter_holds_while_output_high: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        delayed_sys_reset_n |=> $stable(concat_count)
    );

    // The middle byte holds unless the low byte overflows while counting.
    check_mid_byte_holds_without_low_overflow: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        (!delayed_sys_reset_n && (reg_count_7_0 != 8'hff)) |=> (reg_count_15_8 == $past(reg_count_15_8))
    );

    // The middle byte increments when the low byte overflows while counting.
    check_mid_byte_increments_on_low_overflow: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        (!delayed_sys_reset_n && (reg_count_7_0 == 8'hff)) |=> (reg_count_15_8 == ($past(reg_count_15_8) + 8'h01))
    );

    // The high byte holds unless both lower bytes overflow while counting.
    check_high_byte_holds_without_double_overflow: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        (!delayed_sys_reset_n && !((reg_count_15_8 == 8'hff) && (reg_count_7_0 == 8'hff))) |=> (reg_count_23_16 == $past(reg_count_23_16))
    );

    // The high byte increments when both lower bytes overflow while counting.
    check_high_byte_increments_on_double_overflow: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        (!delayed_sys_reset_n && (reg_count_15_8 == 8'hff) && (reg_count_7_0 == 8'hff)) |=> (reg_count_23_16 == ($past(reg_count_23_16) + 8'h01))
    );

    // Once high, the delayed reset remains high until reset is asserted.
    check_output_stays_high_once_asserted: assert property (
        @(posedge ref_clk) disable iff (!sys_reset_n)
        delayed_sys_reset_n |=> delayed_sys_reset_n
    );

endmodule