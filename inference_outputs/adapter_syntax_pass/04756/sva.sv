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

    // Q1 is cleared on the next clock after a sampled reset.
    check_q1_reset: assert property (
        @(posedge CLK) disable iff (CLR)
        $past(CLR) |-> (Q1 == 4'b0000)
    );

    // Q2 is cleared on the next clock after a sampled reset.
    check_q2_reset: assert property (
        @(posedge CLK) disable iff (CLR)
        $past(CLR) |-> (Q2 == 4'b0000)
    );

    // Q1 loads D1 when LD1 is asserted.
    check_q1_load: assert property (
        @(posedge CLK) disable iff (CLR)
        LD1 |=> (Q1 == $past(D1))
    );

    // Q1 shifts left when LD1 is deasserted.
    check_q1_shift: assert property (
        @(posedge CLK) disable iff (CLR)
        !LD1 |=> (Q1 == { $past(Q1[2:0]), $past(Q1[3]) })
    );

    // Q2 loads Q1 when LD2 is asserted.
    check_q2_load: assert property (
        @(posedge CLK) disable iff (CLR)
        LD2 |=> (Q2 == $past(Q1))
    );

    // Q2 shifts left when LD2 is deasserted.
    check_q2_shift: assert property (
        @(posedge CLK) disable iff (CLR)
        !LD2 |=> (Q2 == { $past(Q2[2:0]), $past(Q2[3]) })
    );

    // sum is the 4-bit sum of Q1 and Q2.
    check_sum_matches_inputs: assert property (
        @(posedge CLK) disable iff (CLR)
        sum == (Q1 + Q2)
    );

    // sum is the 4-bit sum of D1 and Q1 when LD2 is deasserted.
    check_sum_when_ld2_low: assert property (
        @(posedge CLK) disable iff (CLR)
        !LD2 |-> (sum == (D1 + Q1))
    );

    // sum is the 4-bit sum of Q1 and Q2 when LD2 is asserted.
    check_sum_when_ld2_high: assert property (
        @(posedge CLK) disable iff (CLR)
        LD2 |-> (sum == (Q1 + Q2))
    );

endmodule