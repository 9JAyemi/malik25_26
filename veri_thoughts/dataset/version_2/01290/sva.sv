module shift_register_sva (
    input logic clk,
    input logic rst,          // active-low reset in RTL (asserted when 0)
    input logic data,
    input logic [2:0] q,
    input logic [2:0] q_temp
);
    // During reset, q must be 0.
    check_reset_clears_q: assert property (
        @(posedge clk) (rst == 1'b0) |-> (q == 3'b000)
    );

    // During reset, q_temp must be 0.
    check_reset_clears_qtemp: assert property (
        @(posedge clk) (rst == 1'b0) |-> (q_temp == 3'b000)
    );

    // q must mirror q_temp at all sampled times.
    check_q_mirrors_qtemp: assert property (
        @(posedge clk) (q == q_temp)
    );

    // On each enabled clock, q shifts left by one and captures data in LSB.
    check_shift_update_word: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (q == { $past(q)[1:0], $past(data) })
    );

    // MSB shift: q[2] takes previous q[1] when enabled.
    check_shift_update_msb: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (q[2] == $past(q[1]))
    );

    // Middle bit shift: q[1] takes previous q[0] when enabled.
    check_shift_update_mid: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (q[1] == $past(q[0]))
    );

    // LSB capture: q[0] takes previous data when enabled.
    check_shift_update_lsb: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (q[0] == $past(data))
    );

    // After three enabled cycles, q equals the last three data samples.
    check_three_cycle_capture: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(rst,1) && $past(rst,2) && $past(rst,3))
            |-> (q == { $past(data,3), $past(data,2), $past(data,1) })
    );

    // While reset is held, q remains zero and stable.
    check_hold_reset_keeps_q_zero: assert property (
        @(posedge clk) (rst == 1'b0 && $past(rst) == 1'b0) |-> (q == 3'b000) && (q == $past(q))
    );

    // While reset is held, q_temp remains zero and stable.
    check_hold_reset_keeps_qtemp_zero: assert property (
        @(posedge clk) (rst == 1'b0 && $past(rst) == 1'b0) |-> (q_temp == 3'b000) && (q_temp == $past(q_temp))
    );
endmodule