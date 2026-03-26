module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] mux_in1,
    input logic [3:0] mux_in2,
    input logic       select,
    input logic [3:0] sum,
    input logic [3:0] counter_out,
    input logic [3:0] mux_out
);

    // Clock: clk
    // Reset: reset, active high
    // Logic: mixed sequential/combinational

    // Counter is cleared whenever reset is sampled high.
    check_counter_zero_during_reset: assert property (
        @(posedge clk) reset |-> (counter_out == 4'h0)
    );

    // Counter remains zero on the first clock after a sampled reset.
    check_counter_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(reset) |-> (counter_out == 4'h0)
    );

    // Nonzero counter values come from incrementing the previous value.
    check_counter_advances_when_nonzero: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && (counter_out != 4'h0)
        |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // A terminal count of 15 is followed by zero on the next sample.
    check_counter_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && ($past(counter_out) == 4'hf)
        |-> (counter_out == 4'h0)
    );

    // The mux drives in1 when select is low.
    check_mux_select_low_routes_in1: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (mux_out == mux_in1)
    );

    // The mux drives in2 when select is high.
    check_mux_select_high_routes_in2: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (mux_out == mux_in2)
    );

    // The adder output matches counter_out plus mux_out.
    check_sum_matches_counter_plus_mux: assert property (
        @(posedge clk) disable iff (reset)
        sum == (counter_out + mux_out)
    );

    // During reset, sum reduces to the currently selected mux input.
    check_sum_matches_selected_input_during_reset: assert property (
        @(posedge clk) reset |-> (sum == (select ? mux_in2 : mux_in1))
    );

    // On the first clock after a sampled reset, sum still reflects zero count.
    check_sum_matches_selected_input_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(reset) |-> (sum == (select ? mux_in2 : mux_in1))
    );

    // With a stable selected input, a nonzero count makes sum advance by one.
    check_sum_advances_with_stable_selected_input: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && $stable(select) &&
        ((select && $stable(mux_in2)) || (!select && $stable(mux_in1))) &&
        (counter_out != 4'h0)
        |-> (sum == ($past(sum) + 4'd1))
    );

    // With a stable selected input, counter wrap makes sum return to that input.
    check_sum_wraps_with_stable_selected_input: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && ($past(counter_out) == 4'hf) &&
        $stable(select) &&
        ((select && $stable(mux_in2)) || (!select && $stable(mux_in1)))
        |-> (sum == (select ? mux_in2 : mux_in1))
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (.*);