module d_flip_flop_mux_sva (
    input logic clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    input logic [7:0] q
);
    // Q updates one negedge later to the sampled muxed input.
    property p_q_updates_to_prev_selected;
        logic [7:0] din;
        @(negedge clk) (din = (sel ? d2 : d1), 1'b1) |=> (q == din);
    endproperty
    check_q_updates_to_prev_selected: assert property (p_q_updates_to_prev_selected);

    // When sel==0 at capture, next q equals sampled d1.
    property p_capture_d1_when_sel0;
        logic [7:0] d1s;
        @(negedge clk) ((sel == 1'b0) ##0 (d1s = d1, 1'b1)) |=> (q == d1s);
    endproperty
    check_capture_d1_when_sel0: assert property (p_capture_d1_when_sel0);

    // When sel==1 at capture, next q equals sampled d2.
    property p_capture_d2_when_sel1;
        logic [7:0] d2s;
        @(negedge clk) ((sel == 1'b1) ##0 (d2s = d2, 1'b1)) |=> (q == d2s);
    endproperty
    check_capture_d2_when_sel1: assert property (p_capture_d2_when_sel1);

    // Next q equals either previously sampled d1 or d2.
    property p_q_equals_prev_d1_or_d2;
        logic [7:0] d1s, d2s;
        @(negedge clk) ((d1s = d1, 1'b1) ##0 (d2s = d2, 1'b1)) |=> ((q == d1s) || (q == d2s));
    endproperty
    check_q_equals_prev_d1_or_d2: assert property (p_q_equals_prev_d1_or_d2);

    // If selected input is unchanged across two captures, q holds its value.
    property p_q_stable_if_selected_stable;
        logic [7:0] din0, din1, q1;
        @(negedge clk)
            (din0 = (sel ? d2 : d1), 1'b1) ##1
            (din1 = (sel ? d2 : d1), q1 = q, 1'b1) |=> ((din1 == din0) |-> (q == q1));
    endproperty
    check_q_stable_if_selected_stable: assert property (p_q_stable_if_selected_stable);

    // If selected input changes across two captures, q must change next.
    property p_q_changes_if_selected_changes;
        logic [7:0] din0, din1, q1;
        @(negedge clk)
            (din0 = (sel ? d2 : d1), 1'b1) ##1
            (din1 = (sel ? d2 : d1), q1 = q, 1'b1) |=> ((din1 != din0) |-> (q != q1));
    endproperty
    check_q_changes_if_selected_changes: assert property (p_q_changes_if_selected_changes);

    // If d1==d2 at capture, next q equals that common value.
    property p_q_equals_common_input_when_equal;
        logic [7:0] v;
        @(negedge clk) ((d1 == d2) ##0 (v = d1, 1'b1)) |=> (q == v);
    endproperty
    check_q_equals_common_input_when_equal: assert property (p_q_equals_common_input_when_equal);

    // With sel held HIGH and d2 stable across captures, q holds steady.
    property p_unselected_d1_ignored_sel_high;
        logic s0, s1;
        logic [7:0] d20, d21, q1;
        @(negedge clk)
            (s0 = sel, d20 = d2, 1'b1) ##1
            (s1 = sel, d21 = d2, q1 = q, 1'b1) |=> (((s0 == 1'b1) && (s1 == 1'b1) && (d21 == d20)) |-> (q == q1));
    endproperty
    check_unselected_d1_ignored_sel_high: assert property (p_unselected_d1_ignored_sel_high);

    // With sel held LOW and d1 stable across captures, q holds steady.
    property p_unselected_d2_ignored_sel_low;
        logic s0, s1;
        logic [7:0] d10, d11, q1;
        @(negedge clk)
            (s0 = sel, d10 = d1, 1'b1) ##1
            (s1 = sel, d11 = d1, q1 = q, 1'b1) |=> (((s0 == 1'b0) && (s1 == 1'b0) && (d11 == d10)) |-> (q == q1));
    endproperty
    check_unselected_d2_ignored_sel_low: assert property (p_unselected_d2_ignored_sel_low);

endmodule