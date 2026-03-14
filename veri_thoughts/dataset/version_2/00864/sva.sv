module priority_encoder_sva (
    input logic clk,
    input logic [7:0] I,
    input logic EN,
    input logic V,
    input logic [2:0] Q
);
    // EN equals reduction-OR of I.
    check_en_matches_or: assert property (
        @(posedge clk) EN == (|I)
    );

    // V is 1 when some but not all bits of I are 1.
    check_v_matches_some_but_not_all: assert property (
        @(posedge clk) V == ((|I) & (~&I))
    );

    // When I is zero, outputs are all zero.
    check_outputs_when_I_zero: assert property (
        @(posedge clk) (I == 8'b0) |-> (EN == 1'b0 && V == 1'b0 && Q == 3'b000)
    );

    // If bit 7 is set, Q wraps to 0 due to i+1 truncation to 3 bits.
    check_q_zero_when_bit7_set: assert property (
        @(posedge clk) I[7] |-> (Q == 3'b000)
    );

    // If highest set bit is 6 (and 7 is 0), Q is 7.
    check_q_when_highest_6: assert property (
        @(posedge clk) (I[7] == 1'b0 && I[6] == 1'b1) |-> (Q == 3'b111)
    );

    // If highest set bit is 5 (and 7:6 are 0), Q is 6.
    check_q_when_highest_5: assert property (
        @(posedge clk) (I[7:6] == 2'b00 && I[5]) |-> (Q == 3'b110)
    );

    // If highest set bit is 4 (and 7:5 are 0), Q is 5.
    check_q_when_highest_4: assert property (
        @(posedge clk) (I[7:5] == 3'b000 && I[4]) |-> (Q == 3'b101)
    );

    // If highest set bit is 3 (and 7:4 are 0), Q is 4.
    check_q_when_highest_3: assert property (
        @(posedge clk) (I[7:4] == 4'b0000 && I[3]) |-> (Q == 3'b100)
    );

    // If highest set bit is 2 (and 7:3 are 0), Q is 3.
    check_q_when_highest_2: assert property (
        @(posedge clk) (I[7:3] == 5'b00000 && I[2]) |-> (Q == 3'b011)
    );

    // If highest set bit is 1 (and 7:2 are 0), Q is 2.
    check_q_when_highest_1: assert property (
        @(posedge clk) (I[7:2] == 6'b000000 && I[1]) |-> (Q == 3'b010)
    );

    // If highest set bit is 0 (and 7:1 are 0), Q is 1.
    check_q_when_highest_0: assert property (
        @(posedge clk) (I[7:1] == 7'b0000000 && I[0]) |-> (Q == 3'b001)
    );
endmodule