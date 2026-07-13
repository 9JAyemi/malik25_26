module mux4_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must match the RTL mux and gating function.
    check_output_matches_rtl_function: assert property (
        @(posedge clk)
        X == (
            (
                ((S1 == 1'b0) && (S0 == 1'b0)) ? A0 :
                ((S1 == 1'b0) && (S0 == 1'b1)) ? A1 :
                ((S1 == 1'b1) && (S0 == 1'b0)) ? A2 :
                A3
            ) &
            ((VGND == 1'b0) ? 1'b0 : VPWR) &
            ((VPB  == 1'b0) ? 1'b0 : VNB)
        )
    );

    // Select 00 routes A0 through the power gating.
    check_select_00_uses_a0: assert property (
        @(posedge clk)
        ((S1 == 1'b0) && (S0 == 1'b0)) |->
        (X == (A0 & ((VGND == 1'b0) ? 1'b0 : VPWR) & ((VPB == 1'b0) ? 1'b0 : VNB)))
    );

    // Select 01 routes A1 through the power gating.
    check_select_01_uses_a1: assert property (
        @(posedge clk)
        ((S1 == 1'b0) && (S0 == 1'b1)) |->
        (X == (A1 & ((VGND == 1'b0) ? 1'b0 : VPWR) & ((VPB == 1'b0) ? 1'b0 : VNB)))
    );

    // Select 10 routes A2 through the power gating.
    check_select_10_uses_a2: assert property (
        @(posedge clk)
        ((S1 == 1'b1) && (S0 == 1'b0)) |->
        (X == (A2 & ((VGND == 1'b0) ? 1'b0 : VPWR) & ((VPB == 1'b0) ? 1'b0 : VNB)))
    );

    // Select 11 routes A3 through the power gating.
    check_select_11_uses_a3: assert property (
        @(posedge clk)
        ((S1 == 1'b1) && (S0 == 1'b1)) |->
        (X == (A3 & ((VGND == 1'b0) ? 1'b0 : VPWR) & ((VPB == 1'b0) ? 1'b0 : VNB)))
    );

    // VGND low forces the output low.
    check_vgnd_low_forces_x_low: assert property (
        @(posedge clk)
        (VGND == 1'b0) |-> (X == 1'b0)
    );

    // VPB low forces the output low.
    check_vpb_low_forces_x_low: assert property (
        @(posedge clk)
        (VPB == 1'b0) |-> (X == 1'b0)
    );

    // With VGND high, low VPWR blocks the output.
    check_vpwr_low_blocks_x: assert property (
        @(posedge clk)
        ((VGND == 1'b1) && (VPWR == 1'b0)) |-> (X == 1'b0)
    );

    // With VPB high, low VNB blocks the output.
    check_vnb_low_blocks_x: assert property (
        @(posedge clk)
        ((VPB == 1'b1) && (VNB == 1'b0)) |-> (X == 1'b0)
    );

    // With all power controls high, X reduces to a plain 4:1 mux.
    check_fully_enabled_path_behaves_as_mux: assert property (
        @(posedge clk)
        ((VGND == 1'b1) && (VPB == 1'b1) && (VPWR == 1'b1) && (VNB == 1'b1)) |->
        (
            X == (
                ((S1 == 1'b0) && (S0 == 1'b0)) ? A0 :
                ((S1 == 1'b0) && (S0 == 1'b1)) ? A1 :
                ((S1 == 1'b1) && (S0 == 1'b0)) ? A2 :
                A3
            )
        )
    );

endmodule