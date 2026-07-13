module complement_sva (
    input logic D,
    input logic Q,
    input logic CLK,
    input logic reg1
);

    // reg1 captures a low D value on the next clock.
    check_reg1_captures_d_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (D === 1'b0) |=> (reg1 === 1'b0)
    );

    // reg1 captures a high D value on the next clock.
    check_reg1_captures_d_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (D === 1'b1) |=> (reg1 === 1'b1)
    );

    // Q captures a low reg1 value on the next clock.
    check_q_captures_reg1_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (reg1 === 1'b0) |=> (Q === 1'b0)
    );

    // Q captures a high reg1 value on the next clock.
    check_q_captures_reg1_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (reg1 === 1'b1) |=> (Q === 1'b1)
    );

    // Q reflects a low D value after two clocks.
    check_q_two_cycle_delay_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (D === 1'b0) |-> ##2 (Q === 1'b0)
    );

    // Q reflects a high D value after two clocks.
    check_q_two_cycle_delay_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (D === 1'b1) |-> ##2 (Q === 1'b1)
    );

endmodule