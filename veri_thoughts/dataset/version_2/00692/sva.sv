module concat_module_sva (
    input logic clk,
    input logic [89:0] in,
    input logic [44:0] line0,
    input logic [44:0] line1,
    input logic [89:0] out
);
    ///// Register capture behavior /////
    // line0 captures the low 45 bits of 'in' from the previous cycle.
    check_line0_captures_low: assert property (
        @(posedge clk) line0 == $past(in[44:0])
    );
    // line1 captures the high 45 bits of 'in' from the previous cycle.
    check_line1_captures_high: assert property (
        @(posedge clk) line1 == $past(in[89:45])
    );

    ///// Output composition from previous cycle registers /////
    // out is the concatenation of the previous values of line0 (MSBs) and line1 (LSBs).
    check_out_from_prev_lines: assert property (
        @(posedge clk) out == $past({line0, line1})
    );
    // The MSBs of out come from the previous line0.
    check_out_msb_from_prev_line0: assert property (
        @(posedge clk) out[89:45] == $past(line0)
    );
    // The LSBs of out come from the previous line1.
    check_out_lsb_from_prev_line1: assert property (
        @(posedge clk) out[44:0] == $past(line1)
    );

    ///// Relation to previous input /////
    // out equals the previous input with halves swapped: {in_low, in_high}.
    check_out_equals_swapped_prev_in: assert property (
        @(posedge clk) out == { $past(in[44:0]), $past(in[89:45]) }
    );
    // The pair {line0,line1} reflects the previous input halves.
    check_lines_match_prev_in_halves: assert property (
        @(posedge clk) {line0, line1} == { $past(in[44:0]), $past(in[89:45]) }
    );

    ///// Change propagation /////
    // A change in the low half of 'in' causes line0 to change next cycle.
    check_low_in_change_propagates_to_line0: assert property (
        @(posedge clk) $changed(in[44:0]) |-> ##1 $changed(line0)
    );
    // A change in the high half of 'in' causes line1 to change next cycle.
    check_high_in_change_propagates_to_line1: assert property (
        @(posedge clk) $changed(in[89:45]) |-> ##1 $changed(line1)
    );
    // Any change in {line0,line1} causes out to change next cycle.
    check_lines_change_propagates_to_out: assert property (
        @(posedge clk) $changed({line0, line1}) |-> ##1 $changed(out)
    );
    // Any change in 'in' causes out to change next cycle (via swapped mapping).
    check_in_change_propagates_to_out: assert property (
        @(posedge clk) $changed(in) |-> ##1 $changed(out)
    );
    // If 'in' is stable across a cycle, out is stable on the next cycle.
    check_stable_in_keeps_out_stable_next: assert property (
        @(posedge clk) $stable(in) |-> ##1 $stable(out)
    );
endmodule