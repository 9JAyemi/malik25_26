module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic q
);

    // q is the XOR of the current and previous selected input values.
    check_q_matches_selected_input_history: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        q == ((sel_b1 ? b : a) ^ $past((sel_b1 ? b : a)))
    );

    // If select stays on a, q reflects the change in a across cycles.
    check_q_when_select_stays_on_a: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!sel_b1 && !$past(sel_b1)) |-> (q == (a ^ $past(a)))
    );

    // If select stays on b, q reflects the change in b across cycles.
    check_q_when_select_stays_on_b: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (sel_b1 && $past(sel_b1)) |-> (q == (b ^ $past(b)))
    );

    // If select switches from a to b, q compares current b to previous a.
    check_q_when_select_switches_a_to_b: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (sel_b1 && !$past(sel_b1)) |-> (q == (b ^ $past(a)))
    );

    // If select switches from b to a, q compares current a to previous b.
    check_q_when_select_switches_b_to_a: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!sel_b1 && $past(sel_b1)) |-> (q == (a ^ $past(b)))
    );

    // q is low when the selected value repeats on consecutive cycles.
    check_q_low_when_selected_value_repeats: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((sel_b1 ? b : a) == $past((sel_b1 ? b : a))) |-> (q == 1'b0)
    );

    // q is high when the selected value changes on consecutive cycles.
    check_q_high_when_selected_value_changes: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((sel_b1 ? b : a) != $past((sel_b1 ? b : a))) |-> (q == 1'b1)
    );

endmodule