module multiplexer16to1_sva (
    input logic [63:0] in,
    input logic [3:0]  SEL,
    input logic [3:0]  out
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // SEL=0000 selects in[3:0].
    check_sel_0000_selects_in_3_0: assert property (
        @($global_clock) (SEL == 4'b0000) |-> (out == in[3:0])
    );

    // SEL=0001 selects in[7:4].
    check_sel_0001_selects_in_7_4: assert property (
        @($global_clock) (SEL == 4'b0001) |-> (out == in[7:4])
    );

    // SEL=0010 selects in[11:8].
    check_sel_0010_selects_in_11_8: assert property (
        @($global_clock) (SEL == 4'b0010) |-> (out == in[11:8])
    );

    // SEL=0011 selects in[15:12].
    check_sel_0011_selects_in_15_12: assert property (
        @($global_clock) (SEL == 4'b0011) |-> (out == in[15:12])
    );

    // SEL=0100 selects in[19:16].
    check_sel_0100_selects_in_19_16: assert property (
        @($global_clock) (SEL == 4'b0100) |-> (out == in[19:16])
    );

    // SEL=0101 selects in[23:20].
    check_sel_0101_selects_in_23_20: assert property (
        @($global_clock) (SEL == 4'b0101) |-> (out == in[23:20])
    );

    // SEL=0110 selects in[27:24].
    check_sel_0110_selects_in_27_24: assert property (
        @($global_clock) (SEL == 4'b0110) |-> (out == in[27:24])
    );

    // SEL=0111 selects in[31:28].
    check_sel_0111_selects_in_31_28: assert property (
        @($global_clock) (SEL == 4'b0111) |-> (out == in[31:28])
    );

    // SEL=1000 selects in[35:32].
    check_sel_1000_selects_in_35_32: assert property (
        @($global_clock) (SEL == 4'b1000) |-> (out == in[35:32])
    );

    // SEL=1001 selects in[39:36].
    check_sel_1001_selects_in_39_36: assert property (
        @($global_clock) (SEL == 4'b1001) |-> (out == in[39:36])
    );

    // SEL=1010 selects in[43:40].
    check_sel_1010_selects_in_43_40: assert property (
        @($global_clock) (SEL == 4'b1010) |-> (out == in[43:40])
    );

    // SEL=1011 selects in[47:44].
    check_sel_1011_selects_in_47_44: assert property (
        @($global_clock) (SEL == 4'b1011) |-> (out == in[47:44])
    );

    // SEL=1100 selects in[51:48].
    check_sel_1100_selects_in_51_48: assert property (
        @($global_clock) (SEL == 4'b1100) |-> (out == in[51:48])
    );

    // SEL=1101 selects in[55:52].
    check_sel_1101_selects_in_55_52: assert property (
        @($global_clock) (SEL == 4'b1101) |-> (out == in[55:52])
    );

    // SEL=1110 selects in[59:56].
    check_sel_1110_selects_in_59_56: assert property (
        @($global_clock) (SEL == 4'b1110) |-> (out == in[59:56])
    );

    // SEL=1111 selects in[63:60].
    check_sel_1111_selects_in_63_60: assert property (
        @($global_clock) (SEL == 4'b1111) |-> (out == in[63:60])
    );

endmodule