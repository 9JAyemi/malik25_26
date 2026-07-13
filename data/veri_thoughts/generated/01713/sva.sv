module BCD7segment_sva (
    input logic clk,
    input logic reset_n,     // External active-low reset for SVA sampling (DUT has no reset)
    input logic [3:0] IN,
    input logic select,
    input logic [6:0] OUT
);
    // OUT must be 1111110 whenever select is LOW.
    select_low_forces_off: assert property (
        @(posedge clk) disable iff (!reset_n) (select == 1'b0) |-> (OUT == 7'b1111110)
    );

    // When select is HIGH and IN==0, OUT must be 0000001.
    map_digit_0: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd0)) |-> (OUT == 7'b0000001)
    );

    // When select is HIGH and IN==1, OUT must be 1001111.
    map_digit_1: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd1)) |-> (OUT == 7'b1001111)
    );

    // When select is HIGH and IN==2, OUT must be 0010010.
    map_digit_2: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd2)) |-> (OUT == 7'b0010010)
    );

    // When select is HIGH and IN==3, OUT must be 0000110.
    map_digit_3: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd3)) |-> (OUT == 7'b0000110)
    );

    // When select is HIGH and IN==4, OUT must be 1001100.
    map_digit_4: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd4)) |-> (OUT == 7'b1001100)
    );

    // When select is HIGH and IN==5, OUT must be 0100100.
    map_digit_5: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd5)) |-> (OUT == 7'b0100100)
    );

    // When select is HIGH and IN==6, OUT must be 0100000.
    map_digit_6: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd6)) |-> (OUT == 7'b0100000)
    );

    // When select is HIGH and IN==7, OUT must be 0001111.
    map_digit_7: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd7)) |-> (OUT == 7'b0001111)
    );

    // When select is HIGH and IN==8, OUT must be 0000000.
    map_digit_8: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd8)) |-> (OUT == 7'b0000000)
    );

    // When select is HIGH and IN==9, OUT must be 0000100.
    map_digit_9: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd9)) |-> (OUT == 7'b0000100)
    );

    // When select is HIGH and IN==10, OUT must be 0001000.
    map_digit_10: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd10)) |-> (OUT == 7'b0001000)
    );

    // When select is HIGH and IN==11, OUT must be 0000000.
    map_digit_11: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd11)) |-> (OUT == 7'b0000000)
    );

    // When select is HIGH and IN==12, OUT must be 0110001.
    map_digit_12: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd12)) |-> (OUT == 7'b0110001)
    );

    // When select is HIGH and IN==13, OUT must be 0000001.
    map_digit_13: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd13)) |-> (OUT == 7'b0000001)
    );

    // When select is HIGH and IN==14, OUT must be 0110000.
    map_digit_14: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd14)) |-> (OUT == 7'b0110000)
    );

    // When select is HIGH and IN==15, OUT must be 0111000.
    map_digit_15: assert property (
        @(posedge clk) disable iff (!reset_n) (select && (IN == 4'd15)) |-> (OUT == 7'b0111000)
    );
endmodule