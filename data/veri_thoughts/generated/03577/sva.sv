module two_bit_counter_assertions (
    input logic CLK,
    input logic RST,
    input logic Q1,
    input logic Q0
);

    // Synchronous reset clears the counter to 00 on the next clock.
    check_reset_clears_to_zero: assert property (
        @(posedge CLK) RST |=> ((Q1 == 1'b0) && (Q0 == 1'b0))
    );

    // State 00 advances to 01 when reset is not asserted.
    check_state_00_to_01: assert property (
        @(posedge CLK) disable iff (RST)
        ((Q1 == 1'b0) && (Q0 == 1'b0)) |=> ((Q1 == 1'b0) && (Q0 == 1'b1))
    );

    // State 01 advances to 10 when reset is not asserted.
    check_state_01_to_10: assert property (
        @(posedge CLK) disable iff (RST)
        ((Q1 == 1'b0) && (Q0 == 1'b1)) |=> ((Q1 == 1'b1) && (Q0 == 1'b0))
    );

    // State 10 advances to 01 when reset is not asserted.
    check_state_10_to_01: assert property (
        @(posedge CLK) disable iff (RST)
        ((Q1 == 1'b1) && (Q0 == 1'b0)) |=> ((Q1 == 1'b0) && (Q0 == 1'b1))
    );

    // State 11 is forced back to 00 on the next clock.
    check_state_11_to_00: assert property (
        @(posedge CLK) disable iff (RST)
        ((Q1 == 1'b1) && (Q0 == 1'b1)) |=> ((Q1 == 1'b0) && (Q0 == 1'b0))
    );

    // The next sampled state is never 11 outside of reset.
    check_next_state_not_11: assert property (
        @(posedge CLK) disable iff (RST)
        1'b1 |=> !((Q1 == 1'b1) && (Q0 == 1'b1))
    );

endmodule