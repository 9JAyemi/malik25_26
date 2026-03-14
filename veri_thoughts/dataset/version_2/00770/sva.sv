module transition_detector_register_sva (
    input logic clk,
    input logic reset,          // active-high synchronous reset
    input logic signal,
    input logic [31:0] output_reg
);
    // Reset sets output_reg to 1 on the next cycle.
    reset_sets_output_reg: assert property (
        @(posedge clk) reset |=> (output_reg == 32'd1)
    );

    // A falling edge of signal (when not in reset) sets output_reg to all 1s on the next cycle.
    fall_sets_all_ones: assert property (
        @(posedge clk) disable iff (reset) $fell(signal) |=> (output_reg == 32'hFFFF_FFFF)
    );

    // Reset has priority over falling-edge detection.
    reset_overrides_fall: assert property (
        @(posedge clk) (reset && $fell(signal)) |=> (output_reg == 32'd1)
    );

    // When not in reset and no falling edge occurs, output_reg holds its value.
    hold_without_fall: assert property (
        @(posedge clk) disable iff (reset) !$fell(signal) |=> (output_reg == $past(output_reg))
    );

    // A rising edge of signal does not change output_reg.
    rise_no_update: assert property (
        @(posedge clk) disable iff (reset) $rose(signal) |=> (output_reg == $past(output_reg))
    );
endmodule