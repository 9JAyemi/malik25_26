module top_module_sva (
    input logic CLK,
    input logic RST,
    input logic UD1,
    input logic LD1,
    input logic [7:0] LOAD_IN1,
    input logic [7:0] Q1,
    input logic UD2,
    input logic LD2,
    input logic [7:0] LOAD_IN2,
    input logic [7:0] Q2,
    input logic [7:0] sum
);

    // Synchronous reset clears both counters and the sum.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) RST |=> (Q1 == 8'h00) && (Q2 == 8'h00) && (sum == 8'h00)
    );

    // The sum output matches the two counter outputs.
    check_sum_matches_q1_q2: assert property (
        @(posedge CLK) disable iff (RST) sum == (Q1 + Q2)
    );

    // LD1 overrides the count direction and loads LOAD_IN1.
    check_q1_load_priority: assert property (
        @(posedge CLK) disable iff (RST) LD1 |=> (Q1 == $past(LOAD_IN1))
    );

    // Without LD1, UD1 high increments Q1.
    check_q1_increment: assert property (
        @(posedge CLK) disable iff (RST) (!LD1 && UD1) |=> (Q1 == ($past(Q1) + 8'd1))
    );

    // Without LD1, UD1 low decrements Q1.
    check_q1_decrement: assert property (
        @(posedge CLK) disable iff (RST) (!LD1 && !UD1) |=> (Q1 == ($past(Q1) - 8'd1))
    );

    // LD2 overrides the count direction and loads LOAD_IN2.
    check_q2_load_priority: assert property (
        @(posedge CLK) disable iff (RST) LD2 |=> (Q2 == $past(LOAD_IN2))
    );

    // Without LD2, UD2 high increments Q2.
    check_q2_increment: assert property (
        @(posedge CLK) disable iff (RST) (!LD2 && UD2) |=> (Q2 == ($past(Q2) + 8'd1))
    );

    // Without LD2, UD2 low decrements Q2.
    check_q2_decrement: assert property (
        @(posedge CLK) disable iff (RST) (!LD2 && !UD2) |=> (Q2 == ($past(Q2) - 8'd1))
    );

endmodule