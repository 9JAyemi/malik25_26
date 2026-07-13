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

    // Reset clears both shift registers and the adder output.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) CLR |-> ((Q1 == 4'b0000) && (Q2 == 4'b0000) && (sum == 4'b0000))
    );

    // The first shift register loads D1 when LD1 is high.
    check_sr1_loads_d1: assert property (
        @(posedge CLK) disable iff (CLR) LD1 |=> (Q1 == $past(D1))
    );

    // The first shift register shifts left when LD1 is low.
    check_sr1_shifts_left: assert property (
        @(posedge CLK) disable iff (CLR) !LD1 |=> (Q1 == {$past(Q1[2:0]), $past(Q1[3])})
    );

    // The second shift register loads Q1 when LD2 is high.
    check_sr2_loads_q1: assert property (
        @(posedge CLK) disable iff (CLR) LD2 |=> (Q2 == $past(Q1))
    );

    // The second shift register shifts left when LD2 is low.
    check_sr2_shifts_left: assert property (
        @(posedge CLK) disable iff (CLR) !LD2 |=> (Q2 == {$past(Q2[2:0]), $past(Q2[3])})
    );

    // The adder output is the sum of the two shift register outputs.
    check_adder_sum: assert property (
        @(posedge CLK) disable iff (CLR) sum == (Q1 + Q2)
    );

    // A left shift in the first stage wraps the previous MSB into bit 0.
    check_sr1_shift_wrap: assert property (
        @(posedge CLK) disable iff (CLR) !LD1 |=> (Q1 == {$past(Q1[2:0]), $past(Q1[3])})
    );

    // A left shift in the second stage wraps the previous MSB into bit 0.
    check_sr2_shift_wrap: assert property (
        @(posedge CLK) disable iff (CLR) !LD2 |=> (Q2 == {$past(Q2[2:0]), $past(Q2[3])})
    );

endmodule