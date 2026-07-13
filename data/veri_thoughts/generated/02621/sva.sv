module amiq_mux2_1_sva (
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);
    // Out equals previous cycle's selected input (registered mux behavior).
    check_out_matches_prev_selected_input: assert property (
        @(posedge clk) disable iff ($initstate) out == $past(sel ? in1 : in0)
    );

    // When previous sel was 0, out equals previous in0.
    check_out_prev_in0_when_prev_sel0: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b0) |-> (out == $past(in0))
    );

    // When previous sel was 1, out equals previous in1.
    check_out_prev_in1_when_prev_sel1: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b1) |-> (out == $past(in1))
    );

    // If both inputs were equal in the previous cycle, out equals that value.
    check_out_when_prev_inputs_equal: assert property (
        @(posedge clk) disable iff ($initstate) ($past(in0) == $past(in1)) |-> (out == $past(in0))
    );

    // If sel is 0 this cycle, next cycle out equals this cycle's in0.
    check_next_out_matches_in0_when_sel0: assert property (
        @(posedge clk) disable iff ($initstate) (sel == 1'b0) |=> (out == $past(in0))
    );

    // If sel is 1 this cycle, next cycle out equals this cycle's in1.
    check_next_out_matches_in1_when_sel1: assert property (
        @(posedge clk) disable iff ($initstate) (sel == 1'b1) |=> (out == $past(in1))
    );
endmodule