module top_module_sva (
    input logic [3:0] D1,
    input logic [3:0] D2,
    input logic       LD1,
    input logic       LD2,
    input logic       CLK,
    input logic       CLR,
    input logic [3:0] sum
);

// Sum is zero whenever CLR is asserted.
    check_sum_zero_on_clear: assert property (
        @(posedge CLK) CLR |-> (sum == 4'b0000)
    );

// With LD1 high, Q1 captures D1 on the next cycle.
    check_q1_loads_d1: assert property (
        @(posedge CLK) disable iff (CLR)
        LD1 |=> (Q1 == $past(D1))
    );

// With LD1 low, Q1 shifts left by one bit on the next cycle.
    check_q1_shifts_left: assert property (
        @(posedge CLK) disable iff (CLR)
        !LD1 |=> (Q1 == {$past(Q1[2:0]), $past(Q1[3])})
    );

// With LD2 high, Q2 captures Q1 on the next cycle.
    check_q2_loads_q1: assert property (
        @(posedge CLK) disable iff (CLR)
        LD2 |=> (Q2 == $past(Q1))
    );

// With LD2 low, Q2 shifts left by one bit on the next cycle.
    check_q2_shifts_left: assert property (
        @(posedge CLK) disable iff (CLR)
        !LD2 |=> (Q2 == {$past(Q2[2:0]), $past(Q2[3])})
    );

// Sum equals Q1 plus Q2 on the next cycle.
    check_sum_equals_q1_plus_q2: assert property (
        @(posedge CLK) disable iff (CLR)
        1'b1 |=> (sum == ($past(Q1) + $past(Q2)))
    );

// With both loads high, Q2 captures D1 on the next cycle.
    check_q2_loads_d1_when_both_loads_high: assert property (
        @(posedge CLK) disable iff (CLR)
        (LD1 && LD2) |=> (Q2 == $past(D1))
    );

// With both loads low, Q2 shifts left by one bit on the next cycle.
    check_q2_shifts_left_when_both_loads_low: assert property (
        @(posedge CLK) disable iff (CLR)
        (!LD1 && !LD2) |=> (Q2 == {$past(Q2[2:0]), $past(Q2[3])})
    );

endmodule
