module mux_pipeline_sva (
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic out,
    input logic clk
);
    ///// Basic port-level checks /////
    // sel is within 0..255 (width-accurate index range).
    check_sel_index_range: assert property (
        @(posedge clk) (sel < 8'd256)
    );
endmodule

module mux_pipeline_int_sva;
    ///// Internal behavior checks /////
    // sel_reg tracks sel combinationally at every clock edge.
    check_sel_reg_matches_sel: assert property (
        @(posedge clk) sel_reg == sel
    );
    // in_next captures previous in_reg each clock.
    check_in_next_from_in_reg: assert property (
        @(posedge clk) in_next == $past(in_reg)
    );
    // in_reg captures previous in_next each clock.
    check_in_reg_from_in_next: assert property (
        @(posedge clk) in_reg == $past(in_next)
    );
    // in_next returns to its value two cycles earlier (swap behavior).
    check_in_next_two_cycle: assert property (
        @(posedge clk) in_next == $past(in_next, 2)
    );
    // in_reg returns to its value two cycles earlier (swap behavior).
    check_in_reg_two_cycle: assert property (
        @(posedge clk) in_reg == $past(in_reg, 2)
    );
    // Concatenated swap: {in_reg,in_next} == $past({in_next,in_reg}).
    check_pair_swap_concat: assert property (
        @(posedge clk) {in_reg, in_next} == $past({in_next, in_reg})
    );
    // out equals the previous cycle's in_next bit selected by previous sel_next.
    check_out_from_prev_in_next_sel_next: assert property (
        @(posedge clk) out == $past(in_next)[ $past(sel_next) ]
    );
    // If selected input and index did not change in the prior step, out must not change.
    check_out_stable_when_inputs_unchanged: assert property (
        @(posedge clk) (($past(in_next) == $past(in_next,2)) && ($past(sel_next) == $past(sel_next,2))) |-> (out == $past(out))
    );
    // If out changed, either in_next or sel_next changed in the prior step.
    check_out_change_implies_input_or_sel_change: assert property (
        @(posedge clk) $changed(out) |-> (($past(in_next) != $past(in_next,2)) || ($past(sel_next) != $past(sel_next,2)))
    );
endmodule

bind mux_pipeline mux_pipeline_int_sva u_mux_pipeline_int_sva ();