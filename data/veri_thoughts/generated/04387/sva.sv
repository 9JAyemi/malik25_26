module multiplexer_16_to_1_sva #(parameter BUS_WIDTH = 32) (
    input logic clk,
    input logic [BUS_WIDTH-1:0] IN1,
    input logic [BUS_WIDTH-1:0] IN2,
    input logic [BUS_WIDTH-1:0] IN3,
    input logic [BUS_WIDTH-1:0] IN4,
    input logic [BUS_WIDTH-1:0] IN5,
    input logic [BUS_WIDTH-1:0] IN6,
    input logic [BUS_WIDTH-1:0] IN7,
    input logic [BUS_WIDTH-1:0] IN8,
    input logic [BUS_WIDTH-1:0] IN9,
    input logic [BUS_WIDTH-1:0] IN10,
    input logic [BUS_WIDTH-1:0] IN11,
    input logic [BUS_WIDTH-1:0] IN12,
    input logic [BUS_WIDTH-1:0] IN13,
    input logic [BUS_WIDTH-1:0] IN14,
    input logic [BUS_WIDTH-1:0] IN15,
    input logic [BUS_WIDTH-1:0] IN16,
    input logic [3:0] SELECT,
    input logic [BUS_WIDTH-1:0] OUT
);

    // SELECT 0 routes IN1 to OUT.
    check_select_0_routes_in1: assert property (
        @(posedge clk) (SELECT == 4'h0) |-> (OUT == IN1)
    );

    // SELECT 1 routes IN2 to OUT.
    check_select_1_routes_in2: assert property (
        @(posedge clk) (SELECT == 4'h1) |-> (OUT == IN2)
    );

    // SELECT 2 routes IN3 to OUT.
    check_select_2_routes_in3: assert property (
        @(posedge clk) (SELECT == 4'h2) |-> (OUT == IN3)
    );

    // SELECT 3 routes IN4 to OUT.
    check_select_3_routes_in4: assert property (
        @(posedge clk) (SELECT == 4'h3) |-> (OUT == IN4)
    );

    // SELECT 4 routes IN5 to OUT.
    check_select_4_routes_in5: assert property (
        @(posedge clk) (SELECT == 4'h4) |-> (OUT == IN5)
    );

    // SELECT 5 routes IN6 to OUT.
    check_select_5_routes_in6: assert property (
        @(posedge clk) (SELECT == 4'h5) |-> (OUT == IN6)
    );

    // SELECT 6 routes IN7 to OUT.
    check_select_6_routes_in7: assert property (
        @(posedge clk) (SELECT == 4'h6) |-> (OUT == IN7)
    );

    // SELECT 7 routes IN8 to OUT.
    check_select_7_routes_in8: assert property (
        @(posedge clk) (SELECT == 4'h7) |-> (OUT == IN8)
    );

    // SELECT 8 routes IN9 to OUT.
    check_select_8_routes_in9: assert property (
        @(posedge clk) (SELECT == 4'h8) |-> (OUT == IN9)
    );

    // SELECT 9 routes IN10 to OUT.
    check_select_9_routes_in10: assert property (
        @(posedge clk) (SELECT == 4'h9) |-> (OUT == IN10)
    );

    // SELECT A routes IN11 to OUT.
    check_select_a_routes_in11: assert property (
        @(posedge clk) (SELECT == 4'hA) |-> (OUT == IN11)
    );

    // SELECT B routes IN12 to OUT.
    check_select_b_routes_in12: assert property (
        @(posedge clk) (SELECT == 4'hB) |-> (OUT == IN12)
    );

    // SELECT C routes IN13 to OUT.
    check_select_c_routes_in13: assert property (
        @(posedge clk) (SELECT == 4'hC) |-> (OUT == IN13)
    );

    // SELECT D routes IN14 to OUT.
    check_select_d_routes_in14: assert property (
        @(posedge clk) (SELECT == 4'hD) |-> (OUT == IN14)
    );

    // SELECT E routes IN15 to OUT.
    check_select_e_routes_in15: assert property (
        @(posedge clk) (SELECT == 4'hE) |-> (OUT == IN15)
    );

    // SELECT F routes IN16 to OUT.
    check_select_f_routes_in16: assert property (
        @(posedge clk) (SELECT == 4'hF) |-> (OUT == IN16)
    );

endmodule