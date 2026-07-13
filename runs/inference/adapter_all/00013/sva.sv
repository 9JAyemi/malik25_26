module mux_4to1_using_2to1_sva (
    input logic        clk,
    input logic [7:0]  data0,
    input logic [7:0]  data1,
    input logic [7:0]  data2,
    input logic [7:0]  data3,
    input logic [1:0]  sel,
    input logic [7:0]  out
);

    // When sel is 00, out must select data0.
    check_sel_00_selects_data0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == data0)
    );

    // When sel is 01, out must select data1.
    check_sel_01_selects_data1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == data1)
    );

    // When sel is 10, out must select data2.
    check_sel_10_selects_data2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == data2)
    );

    // When sel is 11, out must select data3.
    check_sel_11_selects_data3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == data3)
    );

    // With sel[0] low, the upper mux selects the low input pair.
    check_sel0_low_uses_low_pair: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (out == (sel[1] ? data3 : data2))
    );

    // With sel[0] high, the upper mux selects the high input pair.
    check_sel0_high_uses_high_pair: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (out == (sel[1] ? data1 : data0))
    );

    // With sel[1] low, the top-level mux selects the low pair result.
    check_sel1_low_uses_low_pair_result: assert property (
        @(posedge clk) (sel[1] == 1'b0) |-> (out == (sel[0] ? data3 : data2))
    );

    // With sel[1] high, the top-level mux selects the high pair result.
    check_sel1_high_uses_high_pair_result: assert property (
        @(posedge clk) (sel[1] == 1'b1) |-> (out == (sel[0] ? data1 : data0))
    );

endmodule