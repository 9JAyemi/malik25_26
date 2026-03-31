module shift_register_sva (
    input logic [3:0] data_in,
    input logic       shift_clk,
    input logic       reset,
    input logic [3:0] q0,
    input logic [3:0] q1,
    input logic [3:0] q2,
    input logic [3:0] q3
);

// Reset clears all four stages on the next clock.
    check_reset_clears_all: assert property (
        @(posedge shift_clk) reset |=> (q0 == 4'b0000) && (q1 == 4'b0000) && (q2 == 4'b0000) && (q3 == 4'b0000)
    );

// q0 captures data_in on the next clock when reset is low.
    check_q0_captures_data_in: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q0 == $past(data_in))
    );

// q1 captures the previous q0 value on the next clock when reset is low.
    check_q1_captures_prev_q0: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q1 == $past(q0))
    );

// q2 captures the previous q1 value on the next clock when reset is low.
    check_q2_captures_prev_q1: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q2 == $past(q1))
    );

// q3 captures the previous q2 value on the next clock when reset is low.
    check_q3_captures_prev_q2: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |=> (q3 == $past(q2))
    );

// Four consecutive clocks with reset low shift data_in through all four stages.
    check_full_shift_through_all_stages: assert property (
        @(posedge shift_clk) disable iff (reset) 1'b1 |-> ##3 (q0 == $past(data_in,3)) &&
                                                        (q1 == $past(data_in,2)) &&
                                                        (q2 == $past(data_in,1)) &&
                                                        (q3 == $past(data_in))
    );

endmodule
