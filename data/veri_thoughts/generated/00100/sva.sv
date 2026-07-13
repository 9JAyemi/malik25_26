module multiplexer_system_sva (
    input logic        clk,
    input logic [2:0]  sel,
    input logic [3:0]  data0,
    input logic [3:0]  data1,
    input logic [3:0]  data2,
    input logic [3:0]  data3,
    input logic [3:0]  data4,
    input logic [3:0]  data5,
    input logic [3:0]  out
);

    // sel=000 routes data0 to out.
    check_sel_000_routes_data0: assert property (
        @(posedge clk) (sel == 3'b000) |-> (out == data0)
    );

    // sel=001 routes data1 to out.
    check_sel_001_routes_data1: assert property (
        @(posedge clk) (sel == 3'b001) |-> (out == data1)
    );

    // sel=010 routes data2 to out.
    check_sel_010_routes_data2: assert property (
        @(posedge clk) (sel == 3'b010) |-> (out == data2)
    );

    // sel=011 routes data3 to out.
    check_sel_011_routes_data3: assert property (
        @(posedge clk) (sel == 3'b011) |-> (out == data3)
    );

    // sel=100 routes data4 to out.
    check_sel_100_routes_data4: assert property (
        @(posedge clk) (sel == 3'b100) |-> (out == data4)
    );

    // sel=101 routes data5 to out.
    check_sel_101_routes_data5: assert property (
        @(posedge clk) (sel == 3'b101) |-> (out == data5)
    );

    // sel=110 drives the zero-extended reduction-AND result.
    check_sel_110_routes_and_result: assert property (
        @(posedge clk) (sel == 3'b110) |-> (out == {3'b000, &{data5[1:0], data4[1:0], data3[1:0], data2[1:0], data1[1:0], data0[1:0]}})
    );

    // sel=111 drives the same zero-extended reduction-AND result.
    check_sel_111_routes_and_result: assert property (
        @(posedge clk) (sel == 3'b111) |-> (out == {3'b000, &{data5[1:0], data4[1:0], data3[1:0], data2[1:0], data1[1:0], data0[1:0]}})
    );

endmodule