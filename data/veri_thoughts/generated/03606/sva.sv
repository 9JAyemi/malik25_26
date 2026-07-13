module mux_2to1_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    input logic clk,
    input logic reset,
    input logic [3:0] out,
    input logic [3:0] out_a,
    input logic [3:0] out_b
);

    // Reset forces all registered outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |-> (out == 4'h0 && out_a == 4'h0 && out_b == 4'h0)
    );

    // out captures the selected input on the next active clock.
    check_out_captures_selected_input: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (out == ($past(sel) ? $past(B) : $past(A)))
    );

    // out_a captures A when sel is low, otherwise it clears.
    check_out_a_updates_from_a_or_zero: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (out_a == ($past(sel) ? 4'h0 : $past(A)))
    );

    // out_b captures B when sel is high, otherwise it clears.
    check_out_b_updates_from_b_or_zero: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (out_b == ($past(sel) ? $past(B) : 4'h0))
    );

    // At least one auxiliary output is always zero.
    check_aux_outputs_not_both_active: assert property (
        @(posedge clk) disable iff (!reset)
        !$initstate |-> ((out_a == 4'h0) || (out_b == 4'h0))
    );

    // The main output equals the active auxiliary path.
    check_out_equals_or_of_aux_outputs: assert property (
        @(posedge clk) disable iff (!reset)
        !$initstate |-> (out == (out_a | out_b))
    );

endmodule