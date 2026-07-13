module mux_2_to_1_en_sva (
    input logic CLK,
    input logic RESETn,
    input logic a,
    input logic b,
    input logic en,
    input logic out
);
    // Mux functional equivalence: out equals en ? b : a.
    check_mux_func: assert property (
        @(posedge CLK) disable iff (!RESETn) out == (en ? b : a)
    );

    // When en is 1, out mirrors b.
    check_en_selects_b: assert property (
        @(posedge CLK) disable iff (!RESETn) en |-> (out == b)
    );

    // When en is 0, out mirrors a.
    check_en0_selects_a: assert property (
        @(posedge CLK) disable iff (!RESETn) !en |-> (out == a)
    );

    // Out changes only when a, b, or en changes.
    check_out_changes_only_on_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(out) |-> ($changed(a) || $changed(b) || $changed(en))
    );

    // If a, b, and en are stable, out is stable.
    check_stable_inputs_keep_out_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (!$changed(a) && !$changed(b) && !$changed(en)) |-> !$changed(out)
    );

    // With en=1 and b stable, out is stable regardless of a.
    check_en1_b_stable_out_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (en && $stable(en) && $stable(b)) |-> $stable(out)
    );

    // With en=0 and a stable, out is stable regardless of b.
    check_en0_a_stable_out_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (!en && $stable(en) && $stable(a)) |-> $stable(out)
    );

    // Out is independent of a when en=1 and b is stable.
    check_out_independent_of_a_when_en1: assert property (
        @(posedge CLK) disable iff (!RESETn) (en && $stable(en) && $stable(b) && $changed(a)) |-> $stable(out)
    );

    // Out is independent of b when en=0 and a is stable.
    check_out_independent_of_b_when_en0: assert property (
        @(posedge CLK) disable iff (!RESETn) (!en && $stable(en) && $stable(a) && $changed(b)) |-> $stable(out)
    );

    // If a equals b, out equals that value regardless of en.
    check_same_inputs_pass_through: assert property (
        @(posedge CLK) disable iff (!RESETn) (a == b) |-> (out == a)
    );
endmodule