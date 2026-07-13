module not_gate_using_nand_sva (
    input logic clk,
    input logic in,
    input logic out
);

    // RTL has no clock or reset; sample the combinational logic on an external clock.

    // Output matches the NAND of the input with itself.
    check_self_nand_function: assert property (
        @(posedge clk) out === ~(in & in)
    );

    // Output behaves as the inversion of the input.
    check_inverter_function: assert property (
        @(posedge clk) out === ~in
    );

    // A low input drives the output high.
    check_low_input_drives_high: assert property (
        @(posedge clk) (in == 1'b0) |-> (out == 1'b1)
    );

    // A high input drives the output low.
    check_high_input_drives_low: assert property (
        @(posedge clk) (in == 1'b1) |-> (out == 1'b0)
    );

    // A rising input corresponds to a falling output.
    check_input_rise_output_fall: assert property (
        @(posedge clk) $rose(in) |-> $fell(out)
    );

    // A falling input corresponds to a rising output.
    check_input_fall_output_rise: assert property (
        @(posedge clk) $fell(in) |-> $rose(out)
    );

    // If the input is stable across samples, the output is also stable.
    check_stable_input_stable_output: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );

endmodule