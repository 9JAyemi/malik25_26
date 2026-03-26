module shift_register_combination_sva (
    input logic CLK,
    input logic PL1,
    input logic CLR1,
    input logic PL2,
    input logic EN2,
    input logic [3:0] D1,
    input logic [3:0] D2,
    input logic [7:0] Q
);

    // CLR1 clears the upper nibble on the next posedge sample.
    check_reg1_clear: assert property (
        @(posedge CLK) disable iff (1'b0)
        CLR1 |=> (Q[7:4] == 4'b0000)
    );

    // CLR1 has priority over PL1 when both are asserted.
    check_reg1_clear_priority: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLR1 && PL1) |=> (Q[7:4] == 4'b0000)
    );

    // PL1 loads D1 into the upper nibble when CLR1 is low.
    check_reg1_parallel_load: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR1 && PL1) |=> (Q[7:4] == $past(D1))
    );

    // Without CLR1 or PL1, the upper nibble rotates left by one bit.
    check_reg1_rotate: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR1 && !PL1) |=> (Q[7:4] == {$past(Q[6:4]), $past(Q[7])})
    );

    // EN2 loads the lower nibble with D2 on the next negedge sample.
    check_reg2_load_d2: assert property (
        @(negedge CLK) disable iff (1'b0)
        EN2 |=> (Q[3:0] == $past(D2))
    );

    // Without EN2, the lower nibble holds its value across negedges.
    check_reg2_hold: assert property (
        @(negedge CLK) disable iff (1'b0)
        (!EN2) |=> (Q[3:0] == $past(Q[3:0]))
    );

endmodule