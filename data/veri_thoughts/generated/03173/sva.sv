module dmi_jtag_to_core_sync_sva (
    input logic rd_en,
    input logic wr_en,
    input logic rst_n,
    input logic clk,
    input logic reg_en,
    input logic reg_wr_en
);

    // reg_wr_en is always included in reg_en.
    check_reg_wr_en_implies_reg_en: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_wr_en |-> reg_en
    );

    // After reset release, both outputs stay low for two clocks.
    check_reset_release_clears_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        $rose(rst_n) |-> (!reg_en && !reg_wr_en) ##1 (!reg_en && !reg_wr_en)
    );

    // A write rising edge creates a one-cycle reg_wr_en pulse two clocks later.
    check_wr_rise_generates_single_pulse: assert property (
        @(posedge clk) disable iff (!rst_n)
        $rose(wr_en) |-> ##1 (!reg_wr_en) ##1 (reg_wr_en && reg_en) ##1 (!reg_wr_en)
    );

    // A read rising edge drives reg_en two clocks later.
    check_rd_rise_generates_reg_en: assert property (
        @(posedge clk) disable iff (!rst_n)
        $rose(rd_en) |-> ##2 reg_en
    );

    // reg_wr_en cannot remain high on back-to-back clocks.
    check_reg_wr_en_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        reg_wr_en |=> !reg_wr_en
    );

    // reg_wr_en matches the delayed write edge detector.
    check_reg_wr_en_history_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n,1) && $past(rst_n,2) && $past(rst_n,3))
        |-> (reg_wr_en == ($past(wr_en,2) && !$past(wr_en,3)))
    );

    // reg_en matches the OR of the delayed read and write edge detectors.
    check_reg_en_history_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n,1) && $past(rst_n,2) && $past(rst_n,3))
        |-> (reg_en == (($past(wr_en,2) && !$past(wr_en,3)) ||
                        ($past(rd_en,2) && !$past(rd_en,3))))
    );

endmodule