module IBUFDS_GTE3_sva #(
    parameter REFCLK_EN_TX_PATH = 1'b0,
    parameter REFCLK_HROW_CK_SEL = 2'b00,
    parameter REFCLK_ICNTL_RX = 2'b00
) (
    input logic O,
    input logic ODIV2,
    input logic CEB,
    input logic I,
    input logic IB
);

    generate
        if (REFCLK_HROW_CK_SEL == 2'b00) begin : gen_mode00
            // In mode 00, ODIV2 mirrors O.
            check_mode00_odiv2_matches_o: assert property (
                @(posedge I) ODIV2 == O
            );

            // In mode 00, TX path enable or low CEB forces O low.
            check_mode00_force_o_low: assert property (
                @(posedge I) ((REFCLK_EN_TX_PATH == 1'b1) || (CEB == 1'b0)) |-> (O == 1'b0)
            );

            // In mode 00, TX path enable or low CEB forces ODIV2 low.
            check_mode00_force_odiv2_low: assert property (
                @(posedge I) ((REFCLK_EN_TX_PATH == 1'b1) || (CEB == 1'b0)) |-> (ODIV2 == 1'b0)
            );
        end

        if (REFCLK_HROW_CK_SEL == 2'b01) begin : gen_mode01
            // In mode 01, TX path enable forces ODIV2 low.
            check_mode01_tx_path_forces_odiv2_low: assert property (
                @(posedge I) (REFCLK_EN_TX_PATH == 1'b1) |-> (ODIV2 == 1'b0)
            );

            // In mode 01, low CEB forces ODIV2 low.
            check_mode01_ceb_low_forces_odiv2_low: assert property (
                @(posedge I) (CEB == 1'b0) |-> (ODIV2 == 1'b0)
            );

            // In mode 01, ODIV2 can be high only with TX path disabled and CEB high.
            check_mode01_odiv2_high_requires_enabled_path: assert property (
                @(posedge I) (ODIV2 == 1'b1) |-> ((REFCLK_EN_TX_PATH == 1'b0) && (CEB == 1'b1))
            );
        end

        if ((REFCLK_HROW_CK_SEL == 2'b10) || (REFCLK_HROW_CK_SEL == 2'b11)) begin : gen_mode23
            // In modes 10 and 11, ODIV2 is tied low.
            check_mode23_odiv2_tied_low: assert property (
                @(posedge I) ODIV2 == 1'b0
            );
        end
    endgenerate

endmodule