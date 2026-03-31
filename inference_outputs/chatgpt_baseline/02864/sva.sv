module mux2_sva (
    input logic clk,
    input logic sel,
    input logic in1,
    input logic in2,
    input logic out
);
    // Out equals the previously selected input (one-cycle latency behavior).
    check_out_matches_prev_selected: assert property (
        @(posedge clk) $past(1'b1) |-> (out == $past(sel ? in2 : in1))
    );

    // If previous select was 0, out equals previous in1.
    check_prev_sel0_path: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel) == 1'b0) |-> (out == $past(in1))
    );

    // If previous select was 1, out equals previous in2.
    check_prev_sel1_path: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel) == 1'b1) |-> (out == $past(in2))
    );

    // If previous in1 and in2 were equal, out equals that value.
    check_prev_equal_inputs_propagate: assert property (
        @(posedge clk) $past(1'b1) && ($past(in1) == $past(in2)) |-> (out == $past(in1))
    );
endmodule