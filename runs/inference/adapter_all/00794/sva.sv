module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);
    // out_hi captures the previous cycle's upper byte of in.
    check_out_hi_captures_prev_upper: assert property (
        @(posedge clk) disable iff ($initstate) out_hi == $past(in[15:8])
    );

    // out_lo captures the previous cycle's lower byte of in.
    check_out_lo_captures_prev_lower: assert property (
        @(posedge clk) disable iff ($initstate) out_lo == $past(in[7:0])
    );

    // The two outputs together form the previous cycle's input value.
    check_outputs_form_prev_input: assert property (
        @(posedge clk) disable iff ($initstate) {out_hi, out_lo} == $past(in)
    );

    // If in is stable over a cycle, both outputs remain stable.
    check_stable_input_keeps_outputs_stable: assert property (
        @(posedge clk) disable iff ($initstate) $stable(in) |-> ($stable(out_hi) && $stable(out_lo))
    );

    // If in changes between cycles, at least one output changes.
    check_input_change_changes_output: assert property (
        @(posedge clk) disable iff ($initstate) $changed(in) |-> ($changed(out_hi) || $changed(out_lo))
    );

    // If only the upper byte of in changes, only out_hi changes.
    check_upper_change_updates_out_hi_only: assert property (
        @(posedge clk) disable iff ($initstate) ($changed(in[15:8]) && $stable(in[7:0])) |-> ($changed(out_hi) && $stable(out_lo))
    );

    // If only the lower byte of in changes, only out_lo changes.
    check_lower_change_updates_out_lo_only: assert property (
        @(posedge clk) disable iff ($initstate) ($changed(in[7:0]) && $stable(in[15:8])) |-> ($changed(out_lo) && $stable(out_hi))
    );

    // If out_hi changes, the previous cycle's upper byte of in must differ from the current one.
    check_out_hi_change_implies_prev_upper_differs: assert property (
        @(posedge clk) disable iff ($initstate) $changed(out_hi) |-> ($past(in[15:8]) != in[15:8])
    );

    // If out_lo changes, the previous cycle's lower byte of in must differ from the current one.
    check_out_lo_change_implies_prev_lower_differs: assert property (
        @(posedge clk) disable iff ($initstate) $changed(out_lo) |-> ($past(in[7:0]) != in[7:0])
    );

    // If the previous cycle's input was stable, both outputs are stable now.
    check_prev_stable_input_keeps_outputs_stable: assert property (
        @(posedge clk) disable iff ($initstate) $stable($past(in)) |-> ($stable(out_hi) && $stable(out_lo))
    );
endmodule