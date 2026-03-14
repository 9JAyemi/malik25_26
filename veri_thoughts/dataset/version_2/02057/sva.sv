module shift_register_sva (
    input logic in,
    input logic shift,
    input logic out
);
    // Clock: posedge shift. No reset present in RTL. Sequential update on shift edge; out is combinational mirror of register[7].

    // After each shift edge, at the next shift edge out equals the previous in.
    out_lags_in_by_one_shift: assert property (
        @(posedge shift) 1'b1 |=> (out == $past(in))
    );

    // If in toggles between two shift edges, out toggles between the next two shift edges.
    out_toggles_if_in_toggles: assert property (
        @(posedge shift) (in != $past(in)) |=> (out != $past(out))
    );

    // If in is stable across two shift edges, out is stable across the next two shift edges.
    out_stable_if_in_stable: assert property (
        @(posedge shift) (in == $past(in)) |=> (out == $past(out))
    );

    // Out at a given shift edge equals in from the immediately preceding shift edge.
    out_equals_prev_in_same_sample: assert property (
        @(posedge shift) (out == $past(in))
    );

    // If in matches out at a shift edge, then at the next shift edge out remains the same.
    out_holds_when_in_matches: assert property (
        @(posedge shift) (in == out) |=> (out == $past(out))
    );
endmodule