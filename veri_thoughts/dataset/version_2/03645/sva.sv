module logic_circuit_assertions (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out
);

    // Sample the combinational DUT on an external verification clock.

    // Output must match the four-input AND expression.
    check_out_matches_and: assert property (
        @(posedge clk) out === (a & b & c & d)
    );

    // All inputs high drives the output high.
    check_all_high_drives_out_high: assert property (
        @(posedge clk) ((a === 1'b1) && (b === 1'b1) && (c === 1'b1) && (d === 1'b1)) |-> (out === 1'b1)
    );

    // A high output requires all inputs high.
    check_out_high_requires_all_high: assert property (
        @(posedge clk) (out === 1'b1) |-> ((a === 1'b1) && (b === 1'b1) && (c === 1'b1) && (d === 1'b1))
    );

    // Any low input forces the output low.
    check_any_low_forces_out_low: assert property (
        @(posedge clk) ((a === 1'b0) || (b === 1'b0) || (c === 1'b0) || (d === 1'b0)) |-> (out === 1'b0)
    );

    // Stable inputs keep the sampled output stable.
    check_stable_inputs_keep_stable_output: assert property (
        @(posedge clk) $stable({a, b, c, d}) |-> $stable(out)
    );

endmodule