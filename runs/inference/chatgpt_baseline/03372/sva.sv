module mux4to1_sva (
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic       out
);

    // sel=00 selects in[0].
    check_sel_00: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == in[0])
    );

    // sel=01 selects in[1].
    check_sel_01: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == in[1])
    );

    // sel=10 selects in[2].
    check_sel_10: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == in[2])
    );

    // sel=11 selects in[3].
    check_sel_11: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == in[3])
    );

endmodule