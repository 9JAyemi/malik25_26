module mux_converter_sva (
    input logic       clk,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic       o2,
    input logic       o1,
    input logic       o0
);

    // sel=000 selects data0 and inverts bits [3:1].
    check_sel_000_maps_data0: assert property (
        @(posedge clk)
        (sel === 3'b000) |-> ({o2, o1, o0} === ~data0[3:1])
    );

    // sel=001 selects data1 and inverts bits [3:1].
    check_sel_001_maps_data1: assert property (
        @(posedge clk)
        (sel === 3'b001) |-> ({o2, o1, o0} === ~data1[3:1])
    );

    // sel=010 selects data2 and inverts bits [3:1].
    check_sel_010_maps_data2: assert property (
        @(posedge clk)
        (sel === 3'b010) |-> ({o2, o1, o0} === ~data2[3:1])
    );

    // sel=011 selects data3 and inverts bits [3:1].
    check_sel_011_maps_data3: assert property (
        @(posedge clk)
        (sel === 3'b011) |-> ({o2, o1, o0} === ~data3[3:1])
    );

    // sel=100 selects data4 and inverts bits [3:1].
    check_sel_100_maps_data4: assert property (
        @(posedge clk)
        (sel === 3'b100) |-> ({o2, o1, o0} === ~data4[3:1])
    );

    // sel=101 selects data5 and inverts bits [3:1].
    check_sel_101_maps_data5: assert property (
        @(posedge clk)
        (sel === 3'b101) |-> ({o2, o1, o0} === ~data5[3:1])
    );

    // Any unsupported sel value drives all outputs high.
    check_default_sel_drives_ones: assert property (
        @(posedge clk)
        (!((sel === 3'b000) || (sel === 3'b001) || (sel === 3'b010) ||
           (sel === 3'b011) || (sel === 3'b100) || (sel === 3'b101)))
        |-> ({o2, o1, o0} === 3'b111)
    );

endmodule