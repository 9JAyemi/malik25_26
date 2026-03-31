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

    // Reset forces the registered command to its default value.
    check_reset_cmd_default: assert property (
        @(posedge clk_i) !nrst_i |-> (cmd_o == 4'b0111)
    );

    // Reset clears the configuration decode output.
    check_reset_cfg_clear: assert property (
        @(posedge clk_i) !nrst_i |-> (adrcfg_o == 1'b0)
    );

    // Reset clears the memory decode output.
    check_reset_mem_clear: assert property (
        @(posedge clk_i) !nrst_i |-> (adrmem_o == 1'b0)
    );

    // Reset forces the registered upper address bits to their default value.
    check_reset_addr_upper_default: assert property (
        @(posedge clk_i) !nrst_i |-> (adr_o[24:2] == 23'h1fffff)
    );

    // adr_o[1] always reflects the combinational a1 decode from cbe_i[3:2].
    check_adr_lowbit_from_cbe: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (adr_o[1] == ~(cbe_i[3] && cbe_i[2]))
    );

    // Configuration decode requires the registered command bits to match 3'b101.
    check_cfg_decode_requires_cfg_cmd: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adrcfg_o |-> (cmd_o[3:1] == 3'b101)
    );

    // Memory decode requires memEN_i and registered command bits 3'b011.
    check_mem_decode_requires_enable_and_mem_cmd: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adrmem_o |-> (memEN_i && (cmd_o[3:1] == 3'b011))
    );

    // A load captures cbe_i into the registered command output.
    check_cmd_capture_on_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        pciadrLD_i |=> (cmd_o == $past(cbe_i))
    );

    // Without a load, the registered command output holds its value.
    check_cmd_hold_without_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        !pciadrLD_i |=> (cmd_o == $past(cmd_o))
    );

    // A load captures ad_i[24:2] into the registered upper address bits.
    check_addr_upper_capture_on_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        pciadrLD_i |=> (adr_o[24:2] == $past(ad_i[24:2]))
    );

    // Without a load, the registered upper address bits hold their value.
    check_addr_upper_hold_without_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        !pciadrLD_i |=> (adr_o[24:2] == $past(adr_o[24:2]))
    );

    // A load updates config decode from the latched idsel, address, and command.
    check_cfg_decode_after_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        pciadrLD_i |=> (
            adrcfg_o == (
                $past(idsel_i) &&
                ($past(ad_i[1:0]) == 2'b00) &&
                ($past(cbe_i[3:1]) == 3'b101)
            )
        )
    );

    // A load updates memory decode from the latched address and command.
    check_mem_decode_after_load: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        pciadrLD_i |=> (
            adrmem_o == (
                memEN_i &&
                ($past(ad_i[31:25]) == bar0_i) &&
                ($past(ad_i[1:0]) == 2'b00) &&
                ($past(cbe_i[3:1]) == 3'b011)
            )
        )
    );

endmodule