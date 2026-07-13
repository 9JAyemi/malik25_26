module and3_en_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic en,
    input logic out
);
    // Analysis: Clock = posedge en; no reset; sequential FF; out updates on en to a&b&c and holds otherwise.

    // en is HIGH at its own posedge.
    check_en_high_on_posedge: assert property (
        @(posedge en) en == 1'b1
    );

    // On each posedge en (after first), out equals AND of a,b,c from previous posedge.
    check_out_matches_prev_and: assert property (
        @(posedge en) !$isunknown($past({a,b,c})) |-> (out == ($past(a) & $past(b) & $past(c)))
    );

    // If out rises at this posedge, previous a,b,c must all have been 1.
    check_out_rise_requires_prev_and1: assert property (
        @(posedge en) $rose(out) && !$isunknown($past({a,b,c})) |-> ($past(a) && $past(b) && $past(c))
    );

    // If out falls at this posedge, previous a,b,c were not all 1.
    check_out_fall_requires_prev_and0: assert property (
        @(posedge en) $fell(out) && !$isunknown($past({a,b,c})) |-> !($past(a) && $past(b) && $past(c))
    );

    // If previous a,b,c were all 1, out must be 1 at this posedge.
    check_prev_and1_implies_out1: assert property (
        @(posedge en) (!$isunknown($past({a,b,c})) && $past(a) && $past(b) && $past(c)) |-> (out == 1'b1)
    );

    // If previous a,b,c were not all 1, out must be 0 at this posedge.
    check_prev_and0_implies_out0: assert property (
        @(posedge en) (!$isunknown($past({a,b,c})) && !($past(a) && $past(b) && $past(c))) |-> (out == 1'b0)
    );
endmodule