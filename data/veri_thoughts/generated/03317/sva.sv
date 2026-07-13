module xor4_sva (
    input logic clk,
    input logic out,
    input logic a,
    input logic b,
    input logic c,
    input logic d
);

    // Output matches the RTL XOR chain of all four inputs.
    check_out_matches_rtl_xor_chain: assert property (
        @(posedge clk) out == (c ^ d ^ (a ^ b))
    );

    // Output remains stable when all inputs remain stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a, b, c, d}) |-> $stable(out)
    );

    // Output toggles when only input a changes.
    check_out_toggles_when_only_a_changes: assert property (
        @(posedge clk) ($changed(a) && $stable({b, c, d})) |-> $changed(out)
    );

    // Output toggles when only input b changes.
    check_out_toggles_when_only_b_changes: assert property (
        @(posedge clk) ($changed(b) && $stable({a, c, d})) |-> $changed(out)
    );

    // Output toggles when only input c changes.
    check_out_toggles_when_only_c_changes: assert property (
        @(posedge clk) ($changed(c) && $stable({a, b, d})) |-> $changed(out)
    );

    // Output toggles when only input d changes.
    check_out_toggles_when_only_d_changes: assert property (
        @(posedge clk) ($changed(d) && $stable({a, b, c})) |-> $changed(out)
    );

endmodule