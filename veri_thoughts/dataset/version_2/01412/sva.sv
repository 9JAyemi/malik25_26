module binary_counter_sva (
    input logic clk,
    input logic [3:0] count
);

    // From 0, next value must be 1.
    check_count_0_to_1: assert property (
        @(posedge clk) (count == 4'd0) |-> ##1 (count == 4'd1)
    );

    // From 1, next value must be 2.
    check_count_1_to_2: assert property (
        @(posedge clk) (count == 4'd1) |-> ##1 (count == 4'd2)
    );

    // From 2, next value must be 3.
    check_count_2_to_3: assert property (
        @(posedge clk) (count == 4'd2) |-> ##1 (count == 4'd3)
    );

    // From 3, next value must be 4.
    check_count_3_to_4: assert property (
        @(posedge clk) (count == 4'd3) |-> ##1 (count == 4'd4)
    );

    // From 4, next value must be 5.
    check_count_4_to_5: assert property (
        @(posedge clk) (count == 4'd4) |-> ##1 (count == 4'd5)
    );

    // From 5, next value must be 6.
    check_count_5_to_6: assert property (
        @(posedge clk) (count == 4'd5) |-> ##1 (count == 4'd6)
    );

    // From 6, next value must be 7.
    check_count_6_to_7: assert property (
        @(posedge clk) (count == 4'd6) |-> ##1 (count == 4'd7)
    );

    // From 7, next value must be 8.
    check_count_7_to_8: assert property (
        @(posedge clk) (count == 4'd7) |-> ##1 (count == 4'd8)
    );

    // From 8, next value must be 9.
    check_count_8_to_9: assert property (
        @(posedge clk) (count == 4'd8) |-> ##1 (count == 4'd9)
    );

    // From 9, next value must be 10.
    check_count_9_to_10: assert property (
        @(posedge clk) (count == 4'd9) |-> ##1 (count == 4'd10)
    );

    // From 10, next value must be 11.
    check_count_10_to_11: assert property (
        @(posedge clk) (count == 4'd10) |-> ##1 (count == 4'd11)
    );

    // From 11, next value must be 12.
    check_count_11_to_12: assert property (
        @(posedge clk) (count == 4'd11) |-> ##1 (count == 4'd12)
    );

    // From 12, next value must be 13.
    check_count_12_to_13: assert property (
        @(posedge clk) (count == 4'd12) |-> ##1 (count == 4'd13)
    );

    // From 13, next value must be 14.
    check_count_13_to_14: assert property (
        @(posedge clk) (count == 4'd13) |-> ##1 (count == 4'd14)
    );

    // From 14, next value must be 15.
    check_count_14_to_15: assert property (
        @(posedge clk) (count == 4'd14) |-> ##1 (count == 4'd15)
    );

    // From 15, next value must wrap to 0.
    check_count_15_to_0: assert property (
        @(posedge clk) (count == 4'd15) |-> ##1 (count == 4'd0)
    );

endmodule