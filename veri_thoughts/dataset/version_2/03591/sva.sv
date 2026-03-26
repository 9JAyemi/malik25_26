module my_buffer_sva (
    input logic clk,
    input logic i,
    input logic ibar,
    input logic dynamicterminationcontrol,
    input logic out
);

    // Output matches the implemented combinational equation.
    check_output_equation: assert property (
        @(posedge clk) out == (i & ibar & dynamicterminationcontrol)
    );

    // When dynamic termination is disabled, the output is forced low.
    check_disable_forces_zero: assert property (
        @(posedge clk) !dynamicterminationcontrol |-> (out == 1'b0)
    );

    // When enabled, the output follows the AND of i and ibar.
    check_enabled_path_matches_inputs: assert property (
        @(posedge clk) dynamicterminationcontrol |-> (out == (i & ibar))
    );

    // A high output requires all contributing inputs to be high.
    check_high_output_requires_all_inputs_high: assert property (
        @(posedge clk) out |-> (i && ibar && dynamicterminationcontrol)
    );

endmodule