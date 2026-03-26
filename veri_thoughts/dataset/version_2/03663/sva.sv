module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       select,
    input logic [7:0] sum,
    input logic [7:0] mux_out,
    input logic [7:0] final_out
);

    // Reset forces all registered outputs low.
    check_reset_clears_registered_outputs: assert property (
        @(posedge clk) reset |-> ((sum == 8'h00) && (mux_out == 8'h00) && (final_out == 8'h00))
    );

    // First clock after reset release still shows the cleared state.
    check_post_reset_cleared_state: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> ((sum == 8'h00) && (mux_out == 8'h00) && (final_out == 8'h00))
    );

    // Adder output reflects the previous cycle's inputs.
    check_sum_register_update: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (sum == ($past(a) + $past(b)))
    );

    // Mux output reflects the previous cycle's selected input.
    check_mux_register_update: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) &&
         (($past(select) === 1'b0) || ($past(select) === 1'b1))) |->
            (mux_out == ($past(select) ? $past(b) : $past(a)))
    );

    // Mux selects a when select was low.
    check_mux_select_low_path: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(select) === 1'b0)) |-> (mux_out == $past(a))
    );

    // Mux selects b when select was high.
    check_mux_select_high_path: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(select) === 1'b1)) |-> (mux_out == $past(b))
    );

    // OR stage output reflects the previous cycle's sum and mux_out.
    check_final_out_register_update: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (final_out == ($past(sum) | $past(mux_out)))
    );

    // Final output matches the two-stage pipeline from primary inputs.
    check_final_out_end_to_end_pipeline: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past($initstate) && !$past(reset) && !$past(reset, 2) &&
         (($past(select, 2) === 1'b0) || ($past(select, 2) === 1'b1))) |->
            (final_out == (($past(a, 2) + $past(b, 2)) |
                           ($past(select, 2) ? $past(b, 2) : $past(a, 2))))
    );

endmodule