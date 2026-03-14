module shift_register_sva (
    input logic clk,
    input logic reset,   // active-high synchronous reset
    input logic data,
    input logic [2:0] q
);

    // Reset drives q to zero on the active clock edge.
    reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 3'b000)
    );

    // When not in reset, q updates to {previous q[1:0], previous data}.
    shift_vector_update: assert property (
        @(posedge clk) disable iff (reset) q == { $past(q[1:0]), $past(data) }
    );

    // When not in reset, q[0] captures previous data.
    shift_bit0_captures_data: assert property (
        @(posedge clk) disable iff (reset) q[0] == $past(data)
    );

    // When not in reset, q[1] shifts in from previous q[0].
    shift_bit1_from_q0: assert property (
        @(posedge clk) disable iff (reset) q[1] == $past(q[0])
    );

    // When not in reset, q[2] shifts in from previous q[1].
    shift_bit2_from_q1: assert property (
        @(posedge clk) disable iff (reset) q[2] == $past(q[1])
    );

    // On reset deassertion edge, q follows the shift rule from the prior state.
    first_cycle_after_reset: assert property (
        @(posedge clk) $fell(reset) |-> (q == { $past(q[1:0]), $past(data) })
    );

endmodule