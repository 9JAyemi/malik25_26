module pcidec_new_sva (
    input logic        clk_i,
    input logic        nrst_i,
    input logic [31:0] ad_i,
    input logic [3:0]  cbe_i,
    input logic        idsel_i,
    input logic [31:25]bar0_i,
    input logic        memEN_i,
    input logic        pciadrLD_i,
    input logic        adrcfg_o,
    input logic        adrmem_o,
    input logic [24:1] adr_o,
    input logic [3:0]  cmd_o
);

// Reset drives the registered outputs to their default values.
    check_reset_defaults: assert property (
        @(posedge clk_i) !nrst_i |-> (adr_o == 24'h7ffffff) && (cmd_o == 4'h7) && (adrmem_o == 1'b0) && (adrcfg_o == 1'b0)
    );

// adrmem_o is asserted only when the memory access matches the BAR and command pattern.
    check_adrmem_decode: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adrmem_o == ((memEN_i == 1'b1) &&
                     (adr_o[31:25] == bar0_i) &&
                     (adr_o[1:0] == 2'b00) &&
                     (cmd_o == 4'h3))
    );

// adrcfg_o is asserted only when the selected device is in configuration mode.
    check_adrcfg_decode: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adrcfg_o == ((idsel_i == 1'b1) &&
                     (adr_o[1:0] == 2'b00) &&
                     (cmd_o == 4'h5))
    );

// The address output always has the low two bits forced to zero.
    check_adr_low_bits_zero: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adr_o[1:0] == 2'b00
    );

// The address output matches the registered address with the low bits masked out.
    check_adr_mapping: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adr_o[24:2] == $past(ad_i[24:2])
    );

// The command output matches the registered command.
    check_cmd_mapping: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        cmd_o == $past(cbe_i)
    );

// The address output has a1 inverted from the registered cbe[3:2].
    check_a1_inversion: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        adr_o[25] == ~($past(cbe_i[3]) && $past(cbe_i[2]))
    );

// A configuration read request sets the address output to the previous address.
    check_config_read_address: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (idsel_i == 1'b1) && (cbe_i == 4'h5) |=> (adr_o[24:2] == $past(ad_i[24:2]))
    );

// A memory read request sets the address output to the previous address.
    check_memory_read_address: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (memEN_i == 1'b1) && (cbe_i == 4'h3) |=> (adr_o[24:2] == $past(ad_i[24:2]))
    );

// A memory read request with a non-zero BAR offset clears the address output.
    check_memory_read_bar_offset: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (memEN_i == 1'b1) && (cbe_i == 4'h3) && (ad_i[31:25] != bar0_i) |=> (adr_o[24:2] == 23'h0)
    );

// A memory read request with a non-zero byte enable pattern clears the address output.
    check_memory_read_byte_enable: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (memEN_i == 1'b1) && (cbe_i != 4'h3) |=> (adr_o[24:2] == 23'h0)
    );

// A configuration read request with a non-zero byte enable pattern clears the address output.
    check_config_read_byte_enable: assert property (
        @(posedge clk_i) disable iff (!nrst_i)
        (idsel_i == 1'b1) && (cbe_i != 4'h5) |=> (adr_o[24:2] == 23'h0)
    );

endmodule
