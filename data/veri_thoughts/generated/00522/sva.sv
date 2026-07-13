module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic up_down,
    input logic [4:0] final_output,
    input logic [1:0] comparator_output,
    input logic [2:0] up_down_output
);

    // A sampled reset must clear the counter by the next clock.
    check_counter_clears_after_reset: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (up_down_output == 3'b000)
    );

    // An up command increments the counter unless async reset forced it to zero.
    check_counter_counts_up: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        up_down |=> ((up_down_output == ($past(up_down_output) + 3'b001)) ||
                     (up_down_output == 3'b000))
    );

    // A down command decrements the counter unless async reset forced it to zero.
    check_counter_counts_down: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !up_down |=> ((up_down_output == ($past(up_down_output) - 3'b001)) ||
                      (up_down_output == 3'b000))
    );

    // A greater-than comparison produces code 01.
    check_comparator_gt_code: assert property (
        @(posedge clk) disable iff (reset)
        (A > B) |-> (comparator_output == 2'b01)
    );

    // A less-than comparison produces code 10.
    check_comparator_lt_code: assert property (
        @(posedge clk) disable iff (reset)
        (A < B) |-> (comparator_output == 2'b10)
    );

    // Equal inputs produce code 00.
    check_comparator_eq_code: assert property (
        @(posedge clk) disable iff (reset)
        (A == B) |-> (comparator_output == 2'b00)
    );

    // Comparator code 01 selects A for the final sum.
    check_final_selects_a: assert property (
        @(posedge clk) disable iff (reset)
        (comparator_output == 2'b01) |-> (final_output == (up_down_output + A))
    );

    // Comparator code 10 selects B for the final sum.
    check_final_selects_b: assert property (
        @(posedge clk) disable iff (reset)
        (comparator_output == 2'b10) |-> (final_output == (up_down_output + B))
    );

    // All other comparator codes pass the counter value through.
    check_final_default_path: assert property (
        @(posedge clk) disable iff (reset)
        ((comparator_output != 2'b01) && (comparator_output != 2'b10)) |-> (final_output == up_down_output)
    );

    // When A is greater than B, the top-level output adds A.
    check_top_output_when_a_gt_b: assert property (
        @(posedge clk) disable iff (reset)
        (A > B) |-> (final_output == (up_down_output + A))
    );

    // When A is less than B, the top-level output adds B.
    check_top_output_when_a_lt_b: assert property (
        @(posedge clk) disable iff (reset)
        (A < B) |-> (final_output == (up_down_output + B))
    );

    // When A equals B, the top-level output passes the counter through.
    check_top_output_when_a_eq_b: assert property (
        @(posedge clk) disable iff (reset)
        (A == B) |-> (final_output == up_down_output)
    );

endmodule