module port_address_reg_sva
(
    input  logic clk,
    input  logic reset_b,
    input  logic         mem_en,
    input  logic         mem_rd_wr,
    input  logic [01:00] mem_addr,
    input  logic [07:00] mem_wdata,
    input  logic [07:00] mem_rdata,
    input  logic [07:00] address_port_0,
    input  logic [07:00] address_port_1,
    input  logic [07:00] address_port_2,
    input  logic [07:00] address_port_3
);

    ///// Reset behavior /////
    // During active-low reset, address registers hold their reset values.
    reset_defaults: assert property (
        @(posedge clk) !reset_b |-> (address_port_0 == 8'h00) && (address_port_1 == 8'h01) && (address_port_2 == 8'h02) && (address_port_3 == 8'h03)
    );

    ///// Read mux /////
    // mem_addr==2'b00 maps mem_rdata to address_port_0.
    readmux_sel0: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b00) |-> (mem_rdata == address_port_0)
    );
    // mem_addr==2'b01 maps mem_rdata to address_port_1.
    readmux_sel1: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b01) |-> (mem_rdata == address_port_1)
    );
    // mem_addr==2'b10 maps mem_rdata to address_port_2.
    readmux_sel2: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b10) |-> (mem_rdata == address_port_2)
    );
    // mem_addr==2'b11 maps mem_rdata to address_port_3.
    readmux_sel3: assert property (
        @(posedge clk) disable iff (!reset_b) (mem_addr == 2'b11) |-> (mem_rdata == address_port_3)
    );

    ///// Write behavior /////
    // Write to addr 0 updates address_port_0 by next cycle unless immediately rewritten next cycle.
    write_addr0_updates_selected: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && mem_en && mem_rd_wr && (mem_addr == 2'b00)) |=> 
                ( (mem_en && mem_rd_wr && (mem_addr == 2'b00)) ? 1'b1 : (address_port_0 == $past(mem_wdata)) )
    );
    // Write to addr 1 updates address_port_1 by next cycle unless immediately rewritten next cycle.
    write_addr1_updates_selected: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && mem_en && mem_rd_wr && (mem_addr == 2'b01)) |=> 
                ( (mem_en && mem_rd_wr && (mem_addr == 2'b01)) ? 1'b1 : (address_port_1 == $past(mem_wdata)) )
    );
    // Write to addr 2 updates address_port_2 by next cycle unless immediately rewritten next cycle.
    write_addr2_updates_selected: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && mem_en && mem_rd_wr && (mem_addr == 2'b10)) |=> 
                ( (mem_en && mem_rd_wr && (mem_addr == 2'b10)) ? 1'b1 : (address_port_2 == $past(mem_wdata)) )
    );
    // Write to addr 3 updates address_port_3 by next cycle unless immediately rewritten next cycle.
    write_addr3_updates_selected: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && mem_en && mem_rd_wr && (mem_addr == 2'b11)) |=> 
                ( (mem_en && mem_rd_wr && (mem_addr == 2'b11)) ? 1'b1 : (address_port_3 == $past(mem_wdata)) )
    );

    ///// Change qualification /////
    // address_port_0 can change only on a write to addr 0 in the same cycle.
    port0_change_requires_write: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && (address_port_0 != $past(address_port_0))) |-> (mem_en && mem_rd_wr && (mem_addr == 2'b00))
    );
    // address_port_1 can change only on a write to addr 1 in the same cycle.
    port1_change_requires_write: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && (address_port_1 != $past(address_port_1))) |-> (mem_en && mem_rd_wr && (mem_addr == 2'b01))
    );
    // address_port_2 can change only on a write to addr 2 in the same cycle.
    port2_change_requires_write: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && (address_port_2 != $past(address_port_2))) |-> (mem_en && mem_rd_wr && (mem_addr == 2'b10))
    );
    // address_port_3 can change only on a write to addr 3 in the same cycle.
    port3_change_requires_write: assert property (
        @(posedge clk) disable iff (!reset_b)
            ($past(reset_b) && (address_port_3 != $past(address_port_3))) |-> (mem_en && mem_rd_wr && (mem_addr == 2'b11))
    );

endmodule