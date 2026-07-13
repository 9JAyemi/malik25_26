module my_module_sva (
    input logic HI,
    input logic LO,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // HI must match the implemented VPWR/VPB decode.
    check_hi_function: assert property (
        @($global_clock) HI === ((VPWR && !VPB) ? 1'b1 : 1'b0)
    );

    // LO must match the implemented VPWR/VNB decode.
    check_lo_function: assert property (
        @($global_clock) LO === ((!VPWR && !VNB) ? 1'b1 : 1'b0)
    );

    // VPWR high with VPB low must drive HI high.
    check_hi_assert_condition: assert property (
        @($global_clock) (VPWR && !VPB) |-> (HI === 1'b1)
    );

    // VPWR low with VNB low must drive LO high.
    check_lo_assert_condition: assert property (
        @($global_clock) (!VPWR && !VNB) |-> (LO === 1'b1)
    );

    // VPB high must block HI.
    check_vpb_blocks_hi: assert property (
        @($global_clock) VPB |-> (HI === 1'b0)
    );

    // VPWR high must block LO.
    check_vpwr_blocks_lo: assert property (
        @($global_clock) VPWR |-> (LO === 1'b0)
    );

    // HI and LO cannot be high at the same time.
    check_hi_lo_mutex: assert property (
        @($global_clock) !((HI === 1'b1) && (LO === 1'b1))
    );

endmodule