module pcidec_new_sva (
    input logic        clk_i,
    input logic        nrst_i,
    input logic [31:0] ad_i,
    input logic [3:0]  cbe_i,
    input logic        idsel_i,
    input logic [31:25] bar0_i,
    input logic        memEN_i,
    input logic        pciadrLD_i,
    input logic        adrcfg_o,
    input logic        adrmem_o,
    input logic [24:1] adr_o,
    input logic [3:0]  cmd_o
);

    // Reset drives the internal state and outputs to their default values.
    check_reset_defaults: assert property (
        @(posedge clk_i) !nrst_i |-> ((adr_o == 26'h7ffffff) && (cmd_o == 4'h7) && (adrmem_o == 1'b0) && (adrcfg_o == 1'b0))
    );

    // The address output is the stored address with the a1 bit inserted.
    check_adr_o_mapping: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adr_o == { $past(adr), ~($past(cbe_i[3]) && $past(cbe_i[2])) })
    );

    // The command output is the stored command value.
    check_cmd_o_mapping: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (cmd_o == $past(cmd))
    );

    // The memory decode output matches the stored address and command.
    check_adrmem_o_decode: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == (($past(memEN_i) == 1'b1) &&
                      ($past(adr[31:25]) == $past(bar0_i)) &&
                      ($past(adr[1:0]) == 2'b00) &&
                      ($past(cmd[3:1]) == 3'b011)))
    );

    // The configuration decode output matches the stored address and command.
    check_adrcfg_o_decode: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrcfg_o == (($past(idsel_i) == 1'b1) &&
                      ($past(adr[1:0]) == 2'b00) &&
                      ($past(cmd[3:1]) == 3'b101)))
    );

    // A memory decode is never asserted when the memory enable is low.
    check_adrmem_o_requires_memen: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == 1'b0) || ($past(memEN_i) == 1'b1)
    );

    // A memory decode is never asserted when the address is not in the BAR range.
    check_adrmem_o_requires_bar_match: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == 1'b0) || ($past(adr[31:25]) == $past(bar0_i))
    );

    // A memory decode is never asserted when the address LSBs are not zero.
    check_adrmem_o_requires_zero_lsb: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == 1'b0) || ($past(adr[1:0]) == 2'b00)
    );

    // A memory decode is never asserted when the command bits are not 011.
    check_adrmem_o_requires_cmd_code: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == 1'b0) || ($past(cmd[3:1]) == 3'b011)
    );

    // A configuration decode is never asserted when idsel is low.
    check_adrcfg_o_requires_idsel: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrcfg_o == 1'b0) || ($past(idsel_i) == 1'b1)
    );

    // A configuration decode is never asserted when the address LSBs are not zero.
    check_adrcfg_o_requires_zero_lsb: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrcfg_o == 1'b0) || ($past(adr[1:0]) == 2'b00)
    );

    // A configuration decode is never asserted when the command bits are not 101.
    check_adrcfg_o_requires_cmd_code: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrcfg_o == 1'b0) || ($past(cmd[3:1]) == 3'b101)
    );

endmodule