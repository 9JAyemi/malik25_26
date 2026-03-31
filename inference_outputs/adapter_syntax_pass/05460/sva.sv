module shift_register_sva (
    input logic [3:0] data_in,
    input logic       shift_clk,
    input logic       reset,
    input logic [3:0] q0,
    input logic [3:0] q1,
    input logic [3:0] q2,
    input logic [3:0] q3
);

    // Reset clears all stages on the next clock.
    check_reset_clears_all: assert property (
        @(posedge shift_clk) reset |=> (q0 == 4'b0000 && q1 == 4'b0000 && q2 == 4'b0000 && q3 == 4'b0000)
    );

    // q0 captures data_in on each non-reset clock.
    check_q0_captures_data_in: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q0 == $past(data_in))
    );

    // q1 captures the previous q0 value on each non-reset clock.
    check_q1_captures_q0: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q1 == $past(q0))
    );

    // q2 captures the previous q1 value on each non-reset clock.
    check_q2_captures_q1: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q2 == $past(q1))
    );

    // q3 captures the previous q2 value on each non-reset clock.
    check_q3_captures_q2: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q3 == $past(q2))
    );

    // q1 reflects data_in after two non-reset clocks.
    check_q1_two_clock_delay: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> ##1 (q1 == $past(data_in, 2))
    );

    // q2 reflects data_in after three non-reset clocks.
    check_q2_three_clock_delay: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> ##2 (q2 == $past(data_in, 3))
    );

    // q3 reflects data_in after four non-reset clocks.
    check_q3_four_clock_delay: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> ##3 (q3 == $past(data_in, 4))
    );

endmodule