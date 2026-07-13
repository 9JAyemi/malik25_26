module top_module_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic clk,
    input logic out_always
);

    // When both selects are high and b is 1, the output is 1 three clocks later.
    check_b_selected_high: assert property (
        @(posedge clk) (sel_b1 && sel_b2 && (b == 1'b1)) |-> ##3 (out_always == 1'b1)
    );

    // When both selects are high and b is 0, the output is 0 three clocks later.
    check_b_selected_low: assert property (
        @(posedge clk) (sel_b1 && sel_b2 && (b == 1'b0)) |-> ##3 (out_always == 1'b0)
    );

    // When b is not selected and a is 1, the output is 1 three clocks later.
    check_a_selected_high: assert property (
        @(posedge clk) ((!sel_b1 || !sel_b2) && (a == 1'b1)) |-> ##3 (out_always == 1'b1)
    );

    // When b is not selected and a is 0, the output is 0 three clocks later.
    check_a_selected_low: assert property (
        @(posedge clk) ((!sel_b1 || !sel_b2) && (a == 1'b0)) |-> ##3 (out_always == 1'b0)
    );

endmodule