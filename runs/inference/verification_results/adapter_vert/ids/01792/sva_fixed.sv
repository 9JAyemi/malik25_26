module port_address_reg_sva (
    input logic address_port_0,
    input logic address_port_1,
    input logic address_port_2,
    input logic address_port_3,
    input logic clk,
    input logic mem_addr,
    input logic mem_en,
    input logic mem_rd_wr,
    input logic mem_rdata,
    input logic mem_wdata,
    input logic reset_b,
    input logic b00,
    input logic b01,
    input logic b1,
    input logic b10,
    input logic b11,
    input logic h00,
    input logic h01,
    input logic h02,
    input logic h03
);

property ClockSynceotid; @(posedge clk) (mem_addr) == (2'b00) |-> mem_rdata == address_port_0 ; endproperty
assert property (ClockSynceotid);

property ReadSynceotid; @(posedge clk) (mem_addr) == (2'b01) |-> mem_rdata == address_port_1 ; endproperty
assert property (ReadSynceotid);

property WriteSynceotid; @(posedge clk) (mem_addr) == (2'b10) |-> mem_rdata == address_port_2 ; endproperty
assert property (WriteSynceotid);

property WriteSynceotid_2; @(posedge clk) (mem_addr) == (2'b11) |-> mem_rdata == address_port_3 ; endproperty
assert property (WriteSynceotid_2);

property ResetSynceotid; @(posedge clk) (reset_b) != 1'b1  |->  (address_port_0) == 8'h00 && (address_port_1) == 8'h01 && (address_port_2) == 8'h02 && (address_port_3) == 8'h03 ; endproperty
assert property (ResetSynceotid);

property WriteSynceotid_3; @(posedge clk) (reset_b) == 1'b1  && (mem_en) && (mem_rd_wr) |->  (address_port_0) ==  mem_wdata  && (address_port_1) ==  mem_wdata  && (address_port_2) ==  mem_wdata  && (address_port_3) ==  mem_wdata ; endproperty
assert property (WriteSynceotid_3);

endmodule