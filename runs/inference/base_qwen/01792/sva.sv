module port_address_reg_sva (
    input logic clk,
    input logic reset_b,
    input logic mem_en,
    input logic mem_rd_wr,
    input logic [01:00] mem_addr,
    input logic [07:00] mem_wdata,
    output logic [07:00] mem_rdata,
    output logic [07:00] address_port_0,
    output logic [07:00] address_port_1,
    output logic [07:00] address_port_2,
    output logic [07:00] address_port_3
);
    // Sequential logic for address_port_0
    seq_port_0: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_en && mem_rd_wr && mem_addr == 2'b00) |-> address_port_0 == mem_wdata
    );
    // Sequential logic for address_port_1
    seq_port_1: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_en && mem_rd_wr && mem_addr == 2'b01) |-> address_port_1 == mem_wdata
    );
    // Sequential logic for address_port_2
    seq_port_2: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_en && mem_rd_wr && mem_addr == 2'b10) |-> address_port_2 == mem_wdata
    );
    // Sequential logic for address_port_3
    seq_port_3: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_en && mem_rd_wr && mem_addr == 2'b11) |-> address_port_3 == mem_wdata
    );
    // Combinational logic for mem_rdata
    comb_rdata: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b00) |-> mem_rdata == address_port_0
    );
    comb_rdata_1: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b01) |-> mem_rdata == address_port_1
    );
    comb_rdata_2: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b10) |-> mem_rdata == address_port_2
    );
    comb_rdata_3: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b11) |-> mem_rdata == address_port_3
    );
    // Reset behavior
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset_b) !reset_b |-> (address_port_0 == 8'h00) && (address_port_1 == 8'h01) && (address_port_2 == 8'h02) && (address_port_3 == 8'h03)
    );
endmodule