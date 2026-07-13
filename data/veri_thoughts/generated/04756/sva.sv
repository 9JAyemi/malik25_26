module top_module_sva (
    input logic [3:0] D1,
    input logic [3:0] D2,
    input logic       LD1,
    input logic       LD2,
    input logic       CLK,
    input logic       CLR,
    input logic [3:0] sum,
    input logic [3:0] Q1,
    input logic [3:0] Q2
);

    // CLR clears Q1 to zero.
    check_q1_clears_on_clr: assert property (
        @(posedge CLK) CLR |-> (Q1 == 4'b0000)
    );

    // CLR clears Q2 to zero.
    check_q2_clears_on_clr: assert property (
        @(posedge CLK) CLR |-> (Q2 == 4'b0000)
    );

    // During CLR, the summed output is zero.
    check_sum_zero_on_clr: assert property (
        @(posedge CLK) CLR |-> (sum == 4'b0000)
    );

    // LD1 causes Q1 to load D1.
    check_q1_loads_d1: assert property (
        @(posedge CLK) disable iff (CLR) LD1 |=> (Q1 == $past(D1))
    );

    // Without LD1, Q1 rotates left by one bit.
    check_q1_rotates_when_not_loading: assert property (
        @(posedge CLK) disable iff (CLR) !LD1 |=> (Q1 == {$past(Q1[2:0]), $past(Q1[3])})
    );

    // LD2 causes Q2 to load the prior Q1 value.
    check_q2_loads_q1: assert property (
        @(posedge CLK) disable iff (CLR) LD2 |=> (Q2 == $past(Q1))
    );

    // Without LD2, Q2 rotates left by one bit.
    check_q2_rotates_when_not_loading: assert property (
        @(posedge CLK) disable iff (CLR) !LD2 |=> (Q2 == {$past(Q2[2:0]), $past(Q2[3])})
    );

    // The adder output matches Q1 plus Q2.
    check_sum_matches_q1_plus_q2: assert property (
        @(posedge CLK) disable iff (CLR) (sum == (Q1 + Q2))
    );

    // Simultaneous loads use D1 for Q1 and prior Q1 for Q2.
    check_simultaneous_load_behavior: assert property (
        @(posedge CLK) disable iff (CLR) (LD1 && LD2) |=> ((Q1 == $past(D1)) && (Q2 == $past(Q1)))
    );

endmodule