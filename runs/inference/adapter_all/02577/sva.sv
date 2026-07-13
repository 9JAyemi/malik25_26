module mux_4_to_1_sva (
    input logic       clk,
    input logic       sel1,
    input logic       sel2,
    input logic [3:0] d0,
    input logic [3:0] d1,
    input logic [3:0] d2,
    input logic [3:0] d3,
    input logic [3:0] out
);

    // When both selects are high, out must equal d3.
    check_select_11_routes_d3: assert property (
        @(posedge clk) (sel1 && sel2) |-> (out == d3)
    );

    // When select 1 is high and select 2 is low, out must equal d2.
    check_select_10_routes_d2: assert property (
        @(posedge clk) (sel1 && !sel2) |-> (out == d2)
    );

    // When select 1 is low and select 2 is high, out must equal d1.
    check_select_01_routes_d1: assert property (
        @(posedge clk) (!sel1 && sel2) |-> (out == d1)
    );

    // When both selects are low, out must equal d0.
    check_select_00_routes_d0: assert property (
        @(posedge clk) (!sel1 && !sel2) |-> (out == d0)
    );

    // With select 1 high, out must come from the d2/d1 branch.
    check_select_1x_routes_d2_or_d1: assert property (
        @(posedge clk) sel1 |-> (out == (sel2 ? d2 : d1))
    );

    // With select 1 low, out must come from the d1/d0 branch.
    check_select_0x_routes_d1_or_d0: assert property (
        @(posedge clk) !sel1 |-> (out == (sel2 ? d1 : d0))
    );

    // With select 2 high, out must come from the d3/d1 branch.
    check_select_x1_routes_d3_or_d1: assert property (
        @(posedge clk) sel2 |-> (out == (sel1 ? d3 : d1))
    );

    // With select 2 low, out must come from the d2/d0 branch.
    check_select_x0_routes_d2_or_d0: assert property (
        @(posedge clk) !sel2 |-> (out == (sel1 ? d2 : d0))
    );

endmodule