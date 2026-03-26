module top_module_sva(
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic out
);

    // Output matches the RTL's effective combinational function.
    check_out_matches_effective_logic: assert property (
        @($global_clock) out == (in[0] & ~sel[0])
    );

    // sel[0] high forces the output low.
    check_sel0_high_forces_out_low: assert property (
        @($global_clock) (sel[0] == 1'b1) |-> (out == 1'b0)
    );

    // sel[0] low makes the output follow in[0].
    check_sel0_low_passes_in0: assert property (
        @($global_clock) (sel[0] == 1'b0) |-> (out == in[0])
    );

    // A high output requires in[0] high and sel[0] low.
    check_out_high_requires_in0_and_sel0_low: assert property (
        @($global_clock) (out == 1'b1) |-> ((in[0] == 1'b1) && (sel[0] == 1'b0))
    );

    // Changes in other input bits do not affect the output.
    check_other_bits_do_not_affect_out: assert property (
        @($global_clock)
        ($stable(in[0]) && $stable(sel[0]) && $changed({in[255:1], sel[7:1]})) |-> $stable(out)
    );

    // Output changes only when in[0] or sel[0] changes.
    check_out_change_depends_only_on_low_bits: assert property (
        @($global_clock) $changed(out) |-> ($changed(in[0]) || $changed(sel[0]))
    );

endmodule