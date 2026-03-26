module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] in,
    input logic select,
    input logic out,
    input logic bit_change_detector_out,
    input logic [15:0] register_out
);

    // Reset clears the registered data path.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (register_out == 16'h0000)
    );

    // Reset clears the change detector output.
    check_reset_clears_change_flag: assert property (
        @(posedge clk) reset |=> (bit_change_detector_out == 1'b0)
    );

    // Reset drives the top-level output low on the next cycle.
    check_reset_clears_top_out: assert property (
        @(posedge clk) reset |=> (out == 1'b0)
    );

    // While reset stays asserted, all stored outputs remain zero.
    check_sustained_reset_holds_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> ((register_out == 16'h0000) && (bit_change_detector_out == 1'b0) && (out == 1'b0))
    );

    // The register captures the input on the next clock.
    check_register_captures_input: assert property (
        @(posedge clk) disable iff (reset) (!reset) |=> (register_out == $past(in))
    );

    // A change in input raises the detector output on the next cycle.
    check_change_detector_asserts_on_input_change: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (in != $past(in))) |=> (bit_change_detector_out == 1'b1)
    );

    // A stable input keeps the detector output low on the next cycle.
    check_change_detector_deasserts_on_stable_input: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (in == $past(in))) |=> (bit_change_detector_out == 1'b0)
    );

    // When selected, the top output matches the register LSB.
    check_mux_selects_register_lsb: assert property (
        @(posedge clk) disable iff (reset) select |-> (out == register_out[0])
    );

    // When not selected, the top output matches the change detector.
    check_mux_selects_change_detector: assert property (
        @(posedge clk) disable iff (reset) !select |-> (out == bit_change_detector_out)
    );

    // With register selected, output reflects the prior cycle input LSB.
    check_selected_register_reflects_prior_input_lsb: assert property (
        @(posedge clk) disable iff (reset) (select && !$past(reset)) |-> (out == $past(in[0]))
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .select(select),
    .out(out),
    .bit_change_detector_out(bit_change_detector_out),
    .register_out(register_out)
);