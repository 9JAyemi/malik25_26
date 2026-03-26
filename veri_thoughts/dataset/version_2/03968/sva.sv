module romsel_sva (
    input logic        clk,
    input logic [3:0]  selector_i,
    input logic [7:0]  d_o,
    input logic [7:0]  d0_i,
    input logic [7:0]  d1_i,
    input logic [7:0]  d2_i,
    input logic [7:0]  d3_i,
    input logic [7:0]  d4_i,
    input logic [7:0]  d5_i,
    input logic [7:0]  d6_i,
    input logic [7:0]  d7_i,
    input logic [7:0]  d8_i,
    input logic [7:0]  d9_i,
    input logic [7:0]  d10_i,
    input logic [7:0]  d11_i,
    input logic [7:0]  d12_i,
    input logic [7:0]  d13_i,
    input logic [7:0]  d14_i,
    input logic [7:0]  d15_i
);

    // Sampled with an external formal clock; the RTL is combinational and has no reset.

    // selector 0 routes d0_i to d_o.
    check_select_0_routes_d0: assert property (
        @(posedge clk) (selector_i == 4'd0) |-> (d_o == d0_i)
    );

    // selector 1 routes d1_i to d_o.
    check_select_1_routes_d1: assert property (
        @(posedge clk) (selector_i == 4'd1) |-> (d_o == d1_i)
    );

    // selector 2 routes d2_i to d_o.
    check_select_2_routes_d2: assert property (
        @(posedge clk) (selector_i == 4'd2) |-> (d_o == d2_i)
    );

    // selector 3 routes d3_i to d_o.
    check_select_3_routes_d3: assert property (
        @(posedge clk) (selector_i == 4'd3) |-> (d_o == d3_i)
    );

    // selector 4 routes d4_i to d_o.
    check_select_4_routes_d4: assert property (
        @(posedge clk) (selector_i == 4'd4) |-> (d_o == d4_i)
    );

    // selector 5 routes d5_i to d_o.
    check_select_5_routes_d5: assert property (
        @(posedge clk) (selector_i == 4'd5) |-> (d_o == d5_i)
    );

    // selector 6 routes d6_i to d_o.
    check_select_6_routes_d6: assert property (
        @(posedge clk) (selector_i == 4'd6) |-> (d_o == d6_i)
    );

    // selector 7 routes d7_i to d_o.
    check_select_7_routes_d7: assert property (
        @(posedge clk) (selector_i == 4'd7) |-> (d_o == d7_i)
    );

    // selector 8 routes d8_i to d_o.
    check_select_8_routes_d8: assert property (
        @(posedge clk) (selector_i == 4'd8) |-> (d_o == d8_i)
    );

    // selector 9 routes d9_i to d_o.
    check_select_9_routes_d9: assert property (
        @(posedge clk) (selector_i == 4'd9) |-> (d_o == d9_i)
    );

    // selector 10 routes d10_i to d_o.
    check_select_10_routes_d10: assert property (
        @(posedge clk) (selector_i == 4'd10) |-> (d_o == d10_i)
    );

    // selector 11 routes d11_i to d_o.
    check_select_11_routes_d11: assert property (
        @(posedge clk) (selector_i == 4'd11) |-> (d_o == d11_i)
    );

    // selector 12 routes d12_i to d_o.
    check_select_12_routes_d12: assert property (
        @(posedge clk) (selector_i == 4'd12) |-> (d_o == d12_i)
    );

    // selector 13 routes d13_i to d_o.
    check_select_13_routes_d13: assert property (
        @(posedge clk) (selector_i == 4'd13) |-> (d_o == d13_i)
    );

    // selector 14 routes d14_i to d_o.
    check_select_14_routes_d14: assert property (
        @(posedge clk) (selector_i == 4'd14) |-> (d_o == d14_i)
    );

    // selector 15 routes d15_i to d_o.
    check_select_15_routes_d15: assert property (
        @(posedge clk) (selector_i == 4'd15) |-> (d_o == d15_i)
    );

endmodule