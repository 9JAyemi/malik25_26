module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select,
    input logic [7:0] sum,
    input logic [7:0] diff,
    input logic [7:0] abs_diff
);

    // Sum output must equal a plus b.
    check_sum_matches_adder: assert property (
        @(posedge clk) disable iff (reset)
        sum == (a + b)
    );

    // Diff output must equal a minus b.
    check_diff_matches_subtractor: assert property (
        @(posedge clk) disable iff (reset)
        diff == (a - b)
    );

    // Mux must pass sum when select is low.
    check_abs_diff_selects_sum: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (abs_diff == sum)
    );

    // Mux must pass diff when select is high.
    check_abs_diff_selects_diff: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (abs_diff == diff)
    );

    // End-to-end output must equal a plus b when select is low.
    check_abs_diff_matches_add_when_selected: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (abs_diff == (a + b))
    );

    // End-to-end output must equal a minus b when select is high.
    check_abs_diff_matches_sub_when_selected: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (abs_diff == (a - b))
    );

    // Sum must stay stable when a and b stay stable.
    check_sum_stable_for_stable_inputs: assert property (
        @(posedge clk) disable iff (reset)
        ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // Diff must stay stable when a and b stay stable.
    check_diff_stable_for_stable_inputs: assert property (
        @(posedge clk) disable iff (reset)
        ($stable(a) && $stable(b)) |-> $stable(diff)
    );

    // abs_diff must stay stable when all driving inputs stay stable.
    check_abs_diff_stable_for_stable_inputs: assert property (
        @(posedge clk) disable iff (reset)
        ($stable(a) && $stable(b) && $stable(select)) |-> $stable(abs_diff)
    );

    // Changing only select must not affect sum or diff.
    check_select_does_not_change_sum_or_diff: assert property (
        @(posedge clk) disable iff (reset)
        ($stable(a) && $stable(b) && $changed(select)) |-> ($stable(sum) && $stable(diff))
    );

endmodule