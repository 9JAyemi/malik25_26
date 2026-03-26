module and_enable_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic en,
    input logic out
);

    // Output matches the RTL assign expression.
    check_out_definition: assert property (
        @(posedge clk) out === ((en == 1'b1) ? (in1 & in2) : 1'b0)
    );

    // When disabled, the output is forced low.
    check_disable_forces_zero: assert property (
        @(posedge clk) (en === 1'b0) |-> (out === 1'b0)
    );

    // When enabled, the output equals the AND of the inputs.
    check_enabled_matches_and: assert property (
        @(posedge clk) (en === 1'b1) |-> (out === (in1 & in2))
    );

    // A high output requires enable and both inputs high.
    check_out_high_requires_all_high: assert property (
        @(posedge clk) (out === 1'b1) |-> ((en === 1'b1) && (in1 === 1'b1) && (in2 === 1'b1))
    );

    // Enable high with both inputs high drives the output high.
    check_all_high_drives_high: assert property (
        @(posedge clk) ((en === 1'b1) && (in1 === 1'b1) && (in2 === 1'b1)) |-> (out === 1'b1)
    );

    // Enable high with in1 low drives the output low.
    check_in1_low_blocks_output: assert property (
        @(posedge clk) ((en === 1'b1) && (in1 === 1'b0)) |-> (out === 1'b0)
    );

    // Enable high with in2 low drives the output low.
    check_in2_low_blocks_output: assert property (
        @(posedge clk) ((en === 1'b1) && (in2 === 1'b0)) |-> (out === 1'b0)
    );

endmodule