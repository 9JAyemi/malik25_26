module majority_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [7:0] final_output,
    input logic Y,
    input logic [3:0] counter_out,
    input logic [1:0] counter_out_even
);

    // Majority gate output matches the RTL equation.
    check_majority_gate_logic: assert property (
        @(posedge clk) disable iff (reset)
        Y == ((A & B & C) | (A & B & D) | (A & C & D) | (B & C & D))
    );

    // counter_out_even selects counter_out[1:0] when counter_out is odd.
    check_counter_out_even_odd_select: assert property (
        @(posedge clk) disable iff (reset)
        counter_out[0] |-> (counter_out_even == counter_out[1:0])
    );

    // counter_out_even selects counter_out[2:1] when counter_out is even.
    check_counter_out_even_even_select: assert property (
        @(posedge clk) disable iff (reset)
        !counter_out[0] |-> (counter_out_even == counter_out[2:1])
    );

    // The counter clears to zero while reset is asserted.
    check_counter_reset_value: assert property (
        @(posedge clk)
        reset |-> (counter_out == 4'd0)
    );

    // final_output clears to zero while reset is asserted.
    check_final_output_reset_value: assert property (
        @(posedge clk)
        reset |-> (final_output == 8'd0)
    );

    // The counter increments by one on each enabled cycle.
    check_counter_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (counter_out == ($past(counter_out) + 4'd1))
    );

    // The counter holds its value when enable is low.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (counter_out == $past(counter_out))
    );

    // final_output holds its value when enable is low.
    check_final_output_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (final_output == $past(final_output))
    );

    // final_output loads the counter value when the current count is odd.
    check_final_output_loads_counter_on_odd_count: assert property (
        @(posedge clk) disable iff (reset)
        (enable && counter_out[0]) |=> (final_output == {4'b0000, $past(counter_out)})
    );

    // final_output loads the majority result when the current count is even.
    check_final_output_loads_majority_on_even_count: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !counter_out[0]) |=> (final_output == {7'b0000000, $past(Y)})
    );

endmodule