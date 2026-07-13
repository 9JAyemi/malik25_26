module dmi_jtag_to_core_sync_sva (
    input logic       rd_en,
    input logic       wr_en,
    input logic       rst_n,
    input logic       clk,
    input logic       reg_en,
    input logic       reg_wr_en,
    input logic       c_rd_en,
    input logic       c_wr_en,
    input logic [2:0] rden,
    input logic [2:0] wren
);

    // Reset clears the internal state and both outputs.
    check_reset_clears_state: assert property (
        @(posedge clk)
        !rst_n |-> (rden == 3'b000) &&
                  (wren == 3'b000) &&
                  (c_rd_en == 1'b0) &&
                  (c_wr_en == 1'b0) &&
                  (reg_en == 1'b0) &&
                  (reg_wr_en == 1'b0)
    );

    // The read pulse detector matches the decoded rden state.
    check_c_rd_en_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        c_rd_en == (rden[1] & ~rden[2])
    );

    // The write pulse detector matches the decoded wren state.
    check_c_wr_en_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        c_wr_en == (wren[1] & ~wren[2])
    );

    // reg_en is the OR of the read and write pulse detectors.
    check_reg_en_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_en == (c_wr_en | c_rd_en)
    );

    // reg_wr_en directly mirrors the write pulse detector.
    check_reg_wr_en_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_wr_en == c_wr_en
    );

    // A read pulse cannot remain asserted for two sampled clocks.
    check_c_rd_en_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        c_rd_en |=> !c_rd_en
    );

    // A write pulse cannot remain asserted for two sampled clocks.
    check_c_wr_en_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        c_wr_en |=> !c_wr_en
    );

    // reg_wr_en is a single-cycle pulse.
    check_reg_wr_en_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_wr_en |=> !reg_wr_en
    );

    // Any write-enable output pulse must also assert reg_en.
    check_reg_wr_en_implies_reg_en: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_wr_en |-> reg_en
    );

endmodule