module my_uart_rx7to7_sva (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [2:0]  uart_ctl,
    input  logic        rs_rx,
    input  logic [6:0]  data_in,
    input  logic        data_sign
);

    // During reset, outputs are driven low.
    reset_outputs_zero: assert property (
        @(posedge clk) !rst_n |-> (data_in == 7'h0) && (data_sign == 1'b0)
    );

    // On reset deassertion, outputs clear to zero.
    reset_release_clears_outputs: assert property (
        @(posedge clk) $rose(rst_n) |-> (data_in == 7'h0) && (data_sign == 1'b0)
    );

    // Outputs are known (no X/Z) when active.
    outputs_known_when_active: assert property (
        @(posedge clk) disable iff (!rst_n) (!$isunknown(data_in)) && (!$isunknown(data_sign))
    );

    // data_sign is a single-cycle pulse.
    data_sign_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n) (data_sign == 1'b1) |-> ##1 (data_sign == 1'b0)
    );

    // No back-to-back rising edges on data_sign.
    data_sign_no_back_to_back_rise: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(data_sign) |-> ##1 !$rose(data_sign)
    );

    // When data_sign is high, data_in does not change that cycle.
    data_in_stable_when_sign_high: assert property (
        @(posedge clk) disable iff (!rst_n) (data_sign && $past(rst_n)) |-> (data_in == $past(data_in))
    );

    // If data_in changes, data_sign must be LOW that cycle.
    data_in_change_implies_sign_low: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && (data_in != $past(data_in))) |-> (data_sign == 1'b0)
    );

    // At most one bit of data_in can change per cycle.
    data_in_max_one_bit_change: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> $onehot0(data_in ^ $past(data_in))
    );

    // Invalid uart_ctl (6 or 7) forces data_sign LOW in the next cycle.
    invalid_ctl_forces_sign_low_next: assert property (
        @(posedge clk) disable iff (!rst_n) ((uart_ctl == 3'h6) || (uart_ctl == 3'h7)) |-> ##1 (data_sign == 1'b0)
    );

    // data_sign rising requires previous cycle uart_ctl was valid (0..5).
    sign_rise_requires_prev_valid_ctl: assert property (
        @(posedge clk) disable iff (!rst_n) ($rose(data_sign) && $past(rst_n)) |-> (!$past((uart_ctl == 3'h6) || (uart_ctl == 3'h7)))
    );

    // Previous cycle invalid uart_ctl holds data_in stable in this cycle.
    prev_invalid_ctl_keeps_data_in_stable: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && $past((uart_ctl == 3'h6) || (uart_ctl == 3'h7))) |-> (data_in == $past(data_in))
    );

endmodule