module mux_converter_sva (
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic o2,
    input logic o1,
    input logic o0
);

    // sel=000 routes data0[3:1] to the outputs.
    check_sel_000_routes_data0: assert property (
        @($global_clock) (sel == 3'b000) |-> ({o2, o1, o0} == data0[3:1])
    );

    // sel=001 routes data1[3:1] to the outputs.
    check_sel_001_routes_data1: assert property (
        @($global_clock) (sel == 3'b001) |-> ({o2, o1, o0} == data1[3:1])
    );

    // sel=010 routes data2[3:1] to the outputs.
    check_sel_010_routes_data2: assert property (
        @($global_clock) (sel == 3'b010) |-> ({o2, o1, o0} == data2[3:1])
    );

    // sel=011 routes data3[3:1] to the outputs.
    check_sel_011_routes_data3: assert property (
        @($global_clock) (sel == 3'b011) |-> ({o2, o1, o0} == data3[3:1])
    );

    // sel=100 routes data4[3:1] to the outputs.
    check_sel_100_routes_data4: assert property (
        @($global_clock) (sel == 3'b100) |-> ({o2, o1, o0} == data4[3:1])
    );

    // sel=101 routes data5[3:1] to the outputs.
    check_sel_101_routes_data5: assert property (
        @($global_clock) (sel == 3'b101) |-> ({o2, o1, o0} == data5[3:1])
    );

    // Unhandled sel values fall back to data0[3:1].
    check_default_routes_data0: assert property (
        @($global_clock) ((sel == 3'b110) || (sel == 3'b111)) |-> ({o2, o1, o0} == data0[3:1])
    );

endmodule