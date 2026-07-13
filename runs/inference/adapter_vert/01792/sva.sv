property ClockSynceotid; @(posedge clk) (mem_addr) == (2'b00) |-> mem_rdata == address_port_0 ; endproperty 
 
 property ReadSynceotid; @(posedge clk) (mem_addr) == (2'b01) |-> mem_rdata == address_port_1 ; endproperty 
 
 property WriteSynceotid; @(posedge clk) (mem_addr) == (2'b10) |-> mem_rdata == address_port_2 ; endproperty 
 
 property WriteSynceotid; @(posedge clk) (mem_addr) == (2'b11) |-> mem_rdata == address_port_3 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset_b) != 1'b1  |->  (address_port_0) == 8'h00 && (address_port_1) == 8'h01 && (address_port_2) == 8'h02 && (address_port_3) == 8'h03 ; endproperty 
 
 property WriteSynceotid; @(posedge clk) (reset_b) == 1'b1  && (mem_en) && (mem_rd_wr) |->  (address_port_0) ==  mem_wdata  && (address_port_1) ==  mem_wdata  && (address_port_2) ==  mem_wdata  && (address_port_3) ==  mem_wdata ; endproperty 
 