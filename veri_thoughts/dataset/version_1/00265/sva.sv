module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [1:0] B,
    input logic UP,
    input logic DOWN,
    input logic [7:0] q,
    input logic [3:0] shifted,
    input logic [2:0] Q
);

    // B=00 leaves A unchanged.
    check_shift_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (B == 2'b00) |-> (shifted == A)
    );

    // B=01 rotates A left by 1.
    check_shift_rotate_left_1: assert property (
        @(posedge clk) disable iff (reset)
        (B == 2'b01) |-> (shifted == {A[2:0], A[3]})
    );

    // B=10 rotates A left by 2.
    check_shift_rotate_left_2: assert property (
        @(posedge clk) disable iff (reset)
        (B == 2'b10) |-> (shifted == {A[1:0], A[3:2]})
    );

    // B=11 rotates A left by 3.
    check_shift_rotate_left_3: assert property (
        @(posedge clk) disable iff (reset)
        (B == 2'b11) |-> (shifted == {A[0], A[3:1]})
    );

    // Reset clears the counter state.
    check_counter_reset_clears_Q: assert property (
        @(posedge clk)
        reset |=> (Q == 3'b000)
    );

    // UP without DOWN increments the counter.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (reset)
        (UP && !DOWN) |=> (Q == ($past(Q) + 3'b001))
    );

    // DOWN without UP decrements the counter.
    check_counter_decrement: assert property (
        @(posedge clk) disable iff (reset)
        (!UP && DOWN) |=> (Q == ($past(Q) - 3'b001))
    );

    // No request leaves the counter unchanged.
    check_counter_hold_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!UP && !DOWN) |=> (Q == $past(Q))
    );

    // Simultaneous UP and DOWN leaves the counter unchanged.
    check_counter_hold_both_high: assert property (
        @(posedge clk) disable iff (reset)
        (UP && DOWN) |=> (Q == $past(Q))
    );

    // Output q is the sum of shifted and Q with zero extension.
    check_output_sum: assert property (
        @(posedge clk) disable iff (reset)
        (q == ({4'b0000, shifted} + {3'b000, Q}))
    );

endmodule