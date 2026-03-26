module top_module_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic [2:0] D,
    input logic [2:0] Q,
    input logic Q2,
    input logic Q1,
    input logic Q0
);

    // Counter output increments by one when counting up.
    check_counter_count_up: assert property (
        @(posedge clk) disable iff (1'b0)
        up_down |=> (Q == ($past(Q) + 3'b001))
    );

    // Counter output decrements by one when counting down.
    check_counter_count_down: assert property (
        @(posedge clk) disable iff (1'b0)
        !up_down |=> (Q == ($past(Q) - 3'b001))
    );

    // Shift register load drives Q2 from D[2].
    check_shift_load_q2: assert property (
        @(posedge clk) disable iff (1'b0)
        load |=> (Q2 == $past(D[2]))
    );

    // Shift register load drives Q1 from D[2].
    check_shift_load_q1: assert property (
        @(posedge clk) disable iff (1'b0)
        load |=> (Q1 == $past(D[2]))
    );

    // Shift register load drives Q0 from D[2].
    check_shift_load_q0: assert property (
        @(posedge clk) disable iff (1'b0)
        load |=> (Q0 == $past(D[2]))
    );

    // Without load, Q2 shifts in the previous Q1.
    check_shift_step_q2: assert property (
        @(posedge clk) disable iff (1'b0)
        !load |=> (Q2 == $past(Q1))
    );

    // Without load, Q1 shifts in the previous Q0.
    check_shift_step_q1: assert property (
        @(posedge clk) disable iff (1'b0)
        !load |=> (Q1 == $past(Q0))
    );

    // Without load, Q0 captures the previous D[2].
    check_shift_step_q0: assert property (
        @(posedge clk) disable iff (1'b0)
        !load |=> (Q0 == $past(D[2]))
    );

endmodule