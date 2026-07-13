module johnson_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       ena,
    input logic [3:0] q
);

    // Synchronous active-high reset clears q on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 4'b0000)
    );

    // When disabled and not in reset, q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!ena) |=> (q == $past(q))
    );

    // When enabled and not in reset, q[0] follows the RTL next-state equation.
    check_update_q0_when_enabled: assert property (
        @(posedge clk) disable iff (rst) ena |=> (q[0] == ($past(q[3]) ^ (~$past(q[1]))))
    );

    // When enabled and not in reset, q[1] follows the RTL next-state equation.
    check_update_q1_when_enabled: assert property (
        @(posedge clk) disable iff (rst) ena |=> (q[1] == ($past(q[0]) ^ (~$past(q[2]))))
    );

    // When enabled and not in reset, q[2] follows the RTL next-state equation.
    check_update_q2_when_enabled: assert property (
        @(posedge clk) disable iff (rst) ena |=> (q[2] == ($past(q[1]) ^ (~$past(q[3]))))
    );

    // When enabled and not in reset, q[3] follows the RTL next-state equation.
    check_update_q3_when_enabled: assert property (
        @(posedge clk) disable iff (rst) ena |=> (q[3] == ($past(q[2]) ^ (~$past(q[0]))))
    );

endmodule