module dff_3input_sva (
    input logic clk,
    input logic reset,
    input logic set,
    input logic [2:0] data,
    input logic q
);

    // During active-low reset, q must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (q == 1'b0)
    );

    // If reset was low on the previous cycle, q must be 0 now.
    check_prev_reset_low_q_zero: assert property (
        @(posedge clk) $past(!reset) |-> (q == 1'b0)
    );

    // With reset high, set=1 drives q to 1 on the next cycle.
    check_set_forces_one_next: assert property (
        @(posedge clk) disable iff (!reset) set |=> (q == 1'b1)
    );

    // With reset high and set=0, q updates to data[2]&data[1]&data[0] on the next cycle.
    check_data_and_updates_next: assert property (
        @(posedge clk) disable iff (!reset) !set |=> (q == (data[2] & data[1] & data[0]))
    );

    // When the prior cycle was out of reset, q equals (set ? 1 : &data) from the prior cycle.
    check_next_state_equation: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> ( q == ( $past(set) ? 1'b1 : (& $past(data)) ) )
    );

    // If q is 1 now, last cycle must have been out of reset and (set==1 or data==3'b111).
    check_q_one_has_valid_cause: assert property (
        @(posedge clk) disable iff (!reset) (q == 1'b1) |-> ( $past(reset) && ( $past(set) || (& $past(data)) ) )
    );

    // If last cycle had reset high, set=0, and data did not all assert, q must be 0 now.
    check_q_zero_when_prev_inputs_zero: assert property (
        @(posedge clk) disable iff (!reset) ( $past(reset) && !$past(set) && !(& $past(data)) ) |-> (q == 1'b0)
    );

    // While reset is held low across cycles, q stays at 0 and is stable.
    check_q_stable_during_held_reset: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (q == 1'b0 && $stable(q))
    );

endmodule