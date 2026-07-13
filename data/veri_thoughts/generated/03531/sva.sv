module and_with_en_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic en,
    input logic out,
    input logic out_valid
);

    // No DUT clock/reset; this checker samples the combinational interface on clk.

    // out_valid is exactly the enable signal.
    check_out_valid_matches_en: assert property (
        @(posedge clk) out_valid == en
    );

    // out is the AND of both inputs gated by enable.
    check_out_matches_function: assert property (
        @(posedge clk) out == (in1 & in2 & en)
    );

    // When enable is low, out must be low.
    check_disable_forces_out_low: assert property (
        @(posedge clk) !en |-> !out
    );

    // A high out requires both inputs high and enable asserted.
    check_out_high_requires_all_inputs: assert property (
        @(posedge clk) out |-> (in1 && in2 && en && out_valid)
    );

    // When enabled and both inputs are high, out must be high.
    check_enabled_high_inputs_drive_out: assert property (
        @(posedge clk) (en && in1 && in2) |-> out
    );

endmodule