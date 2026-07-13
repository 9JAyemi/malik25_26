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

    // Active-low reset clears the stored address, command, and ID select.
    check_reset_clears_state: assert property (
        @(posedge clk_i)
        !nrst_i |-> ((adr_o == 24'h000001) && (cmd_o == 4'h7) && (adrcfg_o == 1'b0) && (adrmem_o == 1'b0))
    );

    // The output address bus is always the stored address with bit 0 forced high.
    check_adr_o_matches_state: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adr_o == {24'h000001, 1'b1})
    );

    // The command output is always the stored command value.
    check_cmd_o_matches_state: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (cmd_o == 4'h7)
    );

    // The memory enable decoder is always low.
    check_adrmem_o_constant_low: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrmem_o == 1'b0)
    );

    // The configuration decoder is always low.
    check_adrcfg_o_constant_low: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adrcfg_o == 1'b0)
    );

    // The stored address and command remain unchanged when load is not asserted.
    check_state_holds_without_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        !pciadrLD_i |=> ((adr_o == $past(adr_o)) && (cmd_o == $past(cmd_o)))
    );

    // The stored address and command update from the input bus when load is asserted.
    check_state_updates_on_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        pciadrLD_i |=> ((adr_o == {24'h000001, ad_i[24:1]}) && (cmd_o == cbe_i))
    );

endmodule