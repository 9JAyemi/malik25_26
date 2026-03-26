module sky130_fd_sc_hs__decap_sva (
    input logic clk,
    input logic VPWR,
    input logic VGND,
    input logic decap
);

    // decap matches the implemented combinational equation.
    check_decap_equation: assert property (
        @(posedge clk)
        decap === (((VPWR == 1'b0) && (VGND == 1'b1)) ? 1'b1 : 1'b0)
    );

    // decap can only be high when VPWR is low and VGND is high.
    check_decap_high_condition: assert property (
        @(posedge clk)
        (decap === 1'b1) |-> ((VPWR === 1'b0) && (VGND === 1'b1))
    );

    // VPWR low and VGND high must drive decap high.
    check_decap_asserted_for_active_combination: assert property (
        @(posedge clk)
        ((VPWR === 1'b0) && (VGND === 1'b1)) |-> (decap === 1'b1)
    );

    // VPWR high forces decap low.
    check_decap_low_when_vpwr_high: assert property (
        @(posedge clk)
        (VPWR === 1'b1) |-> (decap === 1'b0)
    );

    // VGND low forces decap low.
    check_decap_low_when_vgnd_low: assert property (
        @(posedge clk)
        (VGND === 1'b0) |-> (decap === 1'b0)
    );

endmodule