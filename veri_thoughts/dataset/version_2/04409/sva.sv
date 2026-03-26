module mux_parity_add_sva (
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out,
    input logic parity
);

    // No RTL clock or reset; the design is purely combinational.
    // Assertions are sampled on the formal global clock.

    // sel=000 selects data0 and forms out from the subtract result and upper bits.
    check_sel_000_selects_data0: assert property (
        @($global_clock) (sel == 3'b000) |-> (out == {(data0[1:0] - data0[3:2]), data0[3:2]})
    );

    // sel=001 selects data1 and forms out from the subtract result and upper bits.
    check_sel_001_selects_data1: assert property (
        @($global_clock) (sel == 3'b001) |-> (out == {(data1[1:0] - data1[3:2]), data1[3:2]})
    );

    // sel=010 selects data2 and forms out from the subtract result and upper bits.
    check_sel_010_selects_data2: assert property (
        @($global_clock) (sel == 3'b010) |-> (out == {(data2[1:0] - data2[3:2]), data2[3:2]})
    );

    // sel=011 selects data3 and forms out from the subtract result and upper bits.
    check_sel_011_selects_data3: assert property (
        @($global_clock) (sel == 3'b011) |-> (out == {(data3[1:0] - data3[3:2]), data3[3:2]})
    );

    // sel=100 selects data4 and forms out from the subtract result and upper bits.
    check_sel_100_selects_data4: assert property (
        @($global_clock) (sel == 3'b100) |-> (out == {(data4[1:0] - data4[3:2]), data4[3:2]})
    );

    // sel=101 selects data5 and forms out from the subtract result and upper bits.
    check_sel_101_selects_data5: assert property (
        @($global_clock) (sel == 3'b101) |-> (out == {(data5[1:0] - data5[3:2]), data5[3:2]})
    );

    // sel=110 or 111 drives the default zero output.
    check_invalid_sel_drives_zero: assert property (
        @($global_clock) (sel[2:1] == 2'b11) |-> (out == 4'b0000)
    );

    // sel=110 or 111 produces even parity for the zero output.
    check_invalid_sel_sets_even_parity: assert property (
        @($global_clock) (sel[2:1] == 2'b11) |-> (parity == 1'b1)
    );

    // parity is always the reduction XNOR of out.
    check_parity_matches_out: assert property (
        @($global_clock) parity == ~^out
    );

endmodule