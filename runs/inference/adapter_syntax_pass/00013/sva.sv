module mux_4to1_using_2to1_sva (
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel,
    input logic [7:0] out
);

    // sel=00 routes data0 to out.
    check_sel_00_routes_data0: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == data0)
    );

    // sel=01 routes data1 to out.
    check_sel_01_routes_data1: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == data1)
    );

    // sel=10 routes data2 to out.
    check_sel_10_routes_data2: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == data2)
    );

    // sel=11 routes data3 to out.
    check_sel_11_routes_data3: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == data3)
    );

    // With sel[0] low, the mux behaves as a 2:1 mux of data0/data1.
    check_sel0_mode: assert property (
        @($global_clock) (sel[0] == 1'b0) |-> (out == (sel[1] ? data3 : data2))
    );

    // With sel[0] high, the mux behaves as a 2:1 mux of data1/data2.
    check_sel1_mode: assert property (
        @($global_clock) (sel[0] == 1'b1) |-> (out == (sel[1] ? data3 : data1))
    );

endmodule