module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic [1:0] shift_direction,
    input logic load,
    input logic [7:0] a, b, c, d,
    input logic [7:0] q,
    input logic [7:0] min,
    input logic [7:0] final_output
);

    ///// Reset behavior (active-low) /////
    // While reset is asserted low, q must be 0.
    reset_q_zero: assert property (
        @(posedge clk) !reset |-> (q == 8'h00)
    );

    // While reset is asserted low, final_output must be 0 (since q is 0).
    reset_final_output_zero: assert property (
        @(posedge clk) !reset |-> (final_output == 8'h00)
    );

    ///// Shift register behavior /////
    // On load, q captures data_in on the next cycle.
    load_captures_data: assert property (
        @(posedge clk) disable iff (!reset) load |=> (q == $past(data_in))
    );

    // When not loading and shift_direction==00, q rotates left by 1 on next cycle.
    rotate_left_when_dir00: assert property (
        @(posedge clk) disable iff (!reset)
            (!load && (shift_direction == 2'b00)) |=> (q == { $past(q)[6:0], $past(q)[7] })
    );

    // When not loading and shift_direction==01, q rotates right by 1 on next cycle.
    rotate_right_when_dir01: assert property (
        @(posedge clk) disable iff (!reset)
            (!load && (shift_direction == 2'b01)) |=> (q == { $past(q)[0], $past(q)[7:1] })
    );

    // When not loading and shift_direction is 10 or 11, q holds its value.
    hold_when_dir_others: assert property (
        @(posedge clk) disable iff (!reset)
            (!load && (shift_direction inside {2'b10, 2'b11})) |=> (q == $past(q))
    );

    ///// min_finder (combinational) /////
    // min must be less than or equal to each input.
    min_is_bounded_by_inputs: assert property (
        @(posedge clk) disable iff (!reset) (min <= a) && (min <= b) && (min <= c) && (min <= d)
    );

    // min must equal one of the inputs.
    min_is_one_of_inputs: assert property (
        @(posedge clk) disable iff (!reset) (min == a) || (min == b) || (min == c) || (min == d)
    );

    // If a is less-or-equal to all, min must be a.
    min_selects_a_when_least: assert property (
        @(posedge clk) disable iff (!reset) (a <= b) && (a <= c) && (a <= d) |-> (min == a)
    );

    // If b is strictly less than a and <= c,d, min must be b (reflecting tie-break order).
    min_selects_b_when_least: assert property (
        @(posedge clk) disable iff (!reset) (b < a) && (b <= c) && (b <= d) |-> (min == b)
    );

    ///// Final output /////
    // final_output is the bitwise AND of min and q.
    final_output_is_and: assert property (
        @(posedge clk) disable iff (!reset) final_output == (min & q)
    );

endmodule