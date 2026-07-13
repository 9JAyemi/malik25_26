module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic q
);

    // q captures the mux-selected input on the next rising edge.
    check_q_matches_selected_input: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(sel_b1 ? b : a))
    );

    // When sel_b1 is low, q captures a on the next rising edge.
    check_capture_a_when_sel_low: assert property (
        @(posedge clk) (sel_b1 == 1'b0) |=> (q == $past(a))
    );

    // When sel_b1 is high, q captures b on the next rising edge.
    check_capture_b_when_sel_high: assert property (
        @(posedge clk) (sel_b1 == 1'b1) |=> (q == $past(b))
    );

    // If both mux inputs match, q captures that common value on the next rising edge.
    check_capture_common_input: assert property (
        @(posedge clk) (a == b) |=> (q == $past(a))
    );

endmodule