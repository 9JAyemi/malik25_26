module mux_2_to_1_sva (
    input logic in1,
    input logic in2,
    input logic select,
    input logic out
);
    // On a select edge, if previous select was 0, current out equals previous in1.
    check_prev_sel0_captured_in1: assert property (
        @(posedge select or negedge select) ($past(select) == 1'b0) |-> (out == $past(in1))
    );

    // On a select edge, if previous select was 1, current out equals previous in2.
    check_prev_sel1_captured_in2: assert property (
        @(posedge select or negedge select) ($past(select) == 1'b1) |-> (out == $past(in2))
    );

    // On posedge in1 with no select change since last posedge in1, out must be stable.
    check_out_stable_on_in1_posedge_when_select_stable: assert property (
        @(posedge in1) $stable(select) |-> $stable(out)
    );

    // On negedge in1 with no select change since last negedge in1, out must be stable.
    check_out_stable_on_in1_negedge_when_select_stable: assert property (
        @(negedge in1) $stable(select) |-> $stable(out)
    );

    // On posedge in2 with no select change since last posedge in2, out must be stable.
    check_out_stable_on_in2_posedge_when_select_stable: assert property (
        @(posedge in2) $stable(select) |-> $stable(out)
    );

    // On negedge in2 with no select change since last negedge in2, out must be stable.
    check_out_stable_on_in2_negedge_when_select_stable: assert property (
        @(negedge in2) $stable(select) |-> $stable(out)
    );

    // Sanity: at posedge select, select must read as 1.
    check_select_value_on_posedge: assert property (
        @(posedge select) select == 1'b1
    );

    // Sanity: at negedge select, select must read as 0.
    check_select_value_on_negedge: assert property (
        @(negedge select) select == 1'b0
    );
endmodule