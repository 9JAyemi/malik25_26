module MULTIPLEXER_16_TO_1_sva #(
    parameter BUS_WIDTH = 32
) (
    input logic                    clk,
    input logic [BUS_WIDTH-1:0]    IN1,
    input logic [BUS_WIDTH-1:0]    IN2,
    input logic [BUS_WIDTH-1:0]    IN3,
    input logic [BUS_WIDTH-1:0]    IN4,
    input logic [BUS_WIDTH-1:0]    IN5,
    input logic [BUS_WIDTH-1:0]    IN6,
    input logic [BUS_WIDTH-1:0]    IN7,
    input logic [BUS_WIDTH-1:0]    IN8,
    input logic [BUS_WIDTH-1:0]    IN9,
    input logic [BUS_WIDTH-1:0]    IN10,
    input logic [BUS_WIDTH-1:0]    IN11,
    input logic [BUS_WIDTH-1:0]    IN12,
    input logic [BUS_WIDTH-1:0]    IN13,
    input logic [BUS_WIDTH-1:0]    IN14,
    input logic [BUS_WIDTH-1:0]    IN15,
    input logic [BUS_WIDTH-1:0]    IN16,
    input logic [3:0]              SELECT,
    input logic [BUS_WIDTH-1:0]    OUT
);

    // SELECT 0 must route IN1 to OUT.
    check_select_0_routes_in1: assert property (
        @(posedge clk) (SELECT === 4'b0000) |-> (OUT === IN1)
    );

    // SELECT 1 must route IN2 to OUT.
    check_select_1_routes_in2: assert property (
        @(posedge clk) (SELECT === 4'b0001) |-> (OUT === IN2)
    );

    // SELECT 2 must route IN3 to OUT.
    check_select_2_routes_in3: assert property (
        @(posedge clk) (SELECT === 4'b0010) |-> (OUT === IN3)
    );

    // SELECT 3 must route IN4 to OUT.
    check_select_3_routes_in4: assert property (
        @(posedge clk) (SELECT === 4'b0011) |-> (OUT === IN4)
    );

    // SELECT 4 must route IN5 to OUT.
    check_select_4_routes_in5: assert property (
        @(posedge clk) (SELECT === 4'b0100) |-> (OUT === IN5)
    );

    // SELECT 5 must route IN6 to OUT.
    check_select_5_routes_in6: assert property (
        @(posedge clk) (SELECT === 4'b0101) |-> (OUT === IN6)
    );

    // SELECT 6 must route IN7 to OUT.
    check_select_6_routes_in7: assert property (
        @(posedge clk) (SELECT === 4'b0110) |-> (OUT === IN7)
    );

    // SELECT 7 must route IN8 to OUT.
    check_select_7_routes_in8: assert property (
        @(posedge clk) (SELECT === 4'b0111) |-> (OUT === IN8)
    );

    // SELECT 8 must route IN9 to OUT.
    check_select_8_routes_in9: assert property (
        @(posedge clk) (SELECT === 4'b1000) |-> (OUT === IN9)
    );

    // SELECT 9 must route IN10 to OUT.
    check_select_9_routes_in10: assert property (
        @(posedge clk) (SELECT === 4'b1001) |-> (OUT === IN10)
    );

    // SELECT 10 must route IN11 to OUT.
    check_select_10_routes_in11: assert property (
        @(posedge clk) (SELECT === 4'b1010) |-> (OUT === IN11)
    );

    // SELECT 11 must route IN12 to OUT.
    check_select_11_routes_in12: assert property (
        @(posedge clk) (SELECT === 4'b1011) |-> (OUT === IN12)
    );

    // SELECT 12 must route IN13 to OUT.
    check_select_12_routes_in13: assert property (
        @(posedge clk) (SELECT === 4'b1100) |-> (OUT === IN13)
    );

    // SELECT 13 must route IN14 to OUT.
    check_select_13_routes_in14: assert property (
        @(posedge clk) (SELECT === 4'b1101) |-> (OUT === IN14)
    );

    // SELECT 14 must route IN15 to OUT.
    check_select_14_routes_in15: assert property (
        @(posedge clk) (SELECT === 4'b1110) |-> (OUT === IN15)
    );

    // SELECT 15 must route IN16 to OUT.
    check_select_15_routes_in16: assert property (
        @(posedge clk) (SELECT === 4'b1111) |-> (OUT === IN16)
    );

endmodule