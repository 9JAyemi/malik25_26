module synchronous_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic control,
    input logic [3:0] count
);
    // Synchronous reset clears count to zero on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) reset |-> ##1 (count == 4'b0)
    );

    // While reset is held across cycles, count is zero.
    reset_holds_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'b0)
    );

    // When enable is LOW, count holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |-> ##1 (count == $past(count))
    );

    // When enable and control are HIGH, count increments by 1 on the next cycle.
    inc_on_enable_control: assert property (
        @(posedge clk) disable iff (reset) (enable && control) |-> ##1 (count == $past(count) + 4'd1)
    );

    // When enable is HIGH and control is LOW, count decrements by 1 on the next cycle.
    dec_on_enable_ncontrol: assert property (
        @(posedge clk) disable iff (reset) (enable && !control) |-> ##1 (count == $past(count) - 4'd1)
    );

    // With enable HIGH, count must change on the next cycle.
    change_when_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (count != $past(count))
    );

    // Any change (excluding prior reset) implies previous enable was HIGH.
    change_implies_prev_enable: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (count != $past(count))) |-> $past(enable)
    );

    // If count increased by 1 (excluding prior reset), previous enable && control were HIGH.
    inc_cause_requires_en_ctrl: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (count == $past(count) + 4'd1)) |-> ($past(enable) && $past(control))
    );

    // If count decreased by 1 (excluding prior reset), previous enable was HIGH and control LOW.
    dec_cause_requires_en_nctrl: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (count == $past(count) - 4'd1)) |-> ($past(enable) && !$past(control))
    );

    // Wrap-around on increment: 0xF + 1 -> 0x0 when enabled and control HIGH.
    wrap_inc_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && control && (count == 4'hF)) |-> ##1 (count == 4'h0)
    );

    // Wrap-around on decrement: 0x0 - 1 -> 0xF when enabled and control LOW.
    wrap_dec_from_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && !control && (count == 4'h0)) |-> ##1 (count == 4'hF)
    );

    // LSB toggles whenever an update occurs (enable HIGH).
    lsb_toggles_when_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (count[0] != $past(count[0]))
    );
endmodule