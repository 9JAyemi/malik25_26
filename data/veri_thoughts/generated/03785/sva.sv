module mux_2to1_enable_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       en,
    input logic [7:0] out
);

    // Reset drives the output low.
    check_reset_clears_out: assert property (
        @(posedge clk) !reset |-> (out == 8'b0)
    );

    // Enabled logic selects a when a is nonzero.
    check_select_a_when_enabled_and_a_nonzero: assert property (
        @(posedge clk) disable iff (!reset)
        (en && (a != 8'b0)) |=> (out == $past(a))
    );

    // Enabled logic selects b when a is zero.
    check_select_b_when_enabled_and_a_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (en && (a == 8'b0)) |=> (out == $past(b))
    );

    // Disabled logic clears the output.
    check_zero_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        (!en) |=> (out == 8'b0)
    );

    // Output follows the previous cycle's full decision tree.
    check_full_next_state_function: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (out == ($past(en) ? (($past(a) != 8'b0) ? $past(a) : $past(b)) : 8'b0))
    );

endmodule