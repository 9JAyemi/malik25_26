module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] final_output,
    input logic [3:0] counter_out,
    input logic [2:0] shift_out
);

    // On reset, counter_out is cleared to 0.
    check_counter_reset_value: assert property (
        @(posedge clk) reset |-> (counter_out == 4'b0000)
    );

    // On reset, shift_out is cleared to 0.
    check_shift_reset_value: assert property (
        @(posedge clk) reset |-> (shift_out == 3'b000)
    );

    // When not in reset, counter_out increments by 1 each cycle.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate) (counter_out == ($past(counter_out) + 4'd1))
    );

    // When not in reset, counter_out[0] toggles every cycle.
    check_counter_lsb_toggle: assert property (
        @(posedge clk) disable iff (reset || $initstate) (counter_out[0] == ~$past(counter_out[0]))
    );

    // When not in reset, shift_out shifts left and captures previous counter_out[0].
    check_shift_updates_from_prev: assert property (
        @(posedge clk) disable iff (reset || $initstate) (shift_out == {$past(shift_out[1:0]), $past(counter_out[0])})
    );

    // When not in reset, shift_out[2] takes previous shift_out[1].
    check_shift_bit2_from_prev_bit1: assert property (
        @(posedge clk) disable iff (reset || $initstate) (shift_out[2] == $past(shift_out[1]))
    );

    // When not in reset, shift_out[1] takes previous shift_out[0].
    check_shift_bit1_from_prev_bit0: assert property (
        @(posedge clk) disable iff (reset || $initstate) (shift_out[1] == $past(shift_out[0]))
    );

    // When not in reset, shift_out[0] takes previous counter_out[0].
    check_shift_bit0_from_prev_counter_lsb: assert property (
        @(posedge clk) disable iff (reset || $initstate) (shift_out[0] == $past(counter_out[0]))
    );

    // final_output equals counter_out plus shift_out[2] (zero-extended).
    check_final_output_functional: assert property (
        @(posedge clk) disable iff (reset) (final_output == (counter_out + shift_out[2]))
    );

    // Immediately after reset deasserts, counter_out becomes 1.
    check_counter_after_reset_release_is_one: assert property (
        @(posedge clk) disable iff ($initstate) ($past(reset) && !reset) |-> (counter_out == 4'd1)
    );

    // Immediately after reset deasserts, shift_out is {2'b00, previous counter_out[0]} (thus 0).
    check_shift_after_reset_release_captures_lsb: assert property (
        @(posedge clk) disable iff ($initstate) ($past(reset) && !reset) |-> (shift_out == {2'b00, $past(counter_out[0])})
    );

endmodule