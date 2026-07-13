module port_address_reg_sva (
    input logic        clk,
    input logic        reset_b,
    input logic        mem_en,
    input logic        mem_rd_wr,
    input logic [1:0]  mem_addr,
    input logic [7:0]  mem_wdata,
    input logic [7:0]  mem_rdata,
    input logic [7:0]  address_port_0,
    input logic [7:0]  address_port_1,
    input logic [7:0]  address_port_2,
    input logic [7:0]  address_port_3
);

// Active-low reset clears all port addresses to their default values.
    check_reset_defaults: assert property (
        @(posedge clk) !reset_b |-> (address_port_0 == 8'h00 &&
                                    address_port_1 == 8'h01 &&
                                    address_port_2 == 8'h02 &&
                                    address_port_3 == 8'h03)
    );

// Read address 0 returns port 0's value.
    check_read_addr_0: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_addr == 2'd0) |-> (mem_rdata == address_port_0)
    );

// Read address 1 returns port 1's value.
    check_read_addr_1: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_addr == 2'd1) |-> (mem_rdata == address_port_1)
    );

// Read address 2 returns port 2's value.
    check_read_addr_2: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_addr == 2'd2) |-> (mem_rdata == address_port_2)
    );

// Read address 3 returns port 3's value.
    check_read_addr_3: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_addr == 2'd3) |-> (mem_rdata == address_port_3)
    );

// Write to address 0 updates port 0 on the next cycle.
    check_write_addr_0: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_en && mem_rd_wr && (mem_addr == 2'd0)) |=> (address_port_0 == $past(mem_wdata))
    );

// Write to address 1 updates port 1 on the next cycle.
    check_write_addr_1: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_en && mem_rd_wr && (mem_addr == 2'd1)) |=> (address_port_1 == $past(mem_wdata))
    );

// Write to address 2 updates port 2 on the next cycle.
    check_write_addr_2: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_en && mem_rd_wr && (mem_addr == 2'd2)) |=> (address_port_2 == $past(mem_wdata))
    );

// Write to address 3 updates port 3 on the next cycle.
    check_write_addr_3: assert property (
        @(posedge clk) disable iff (!reset_b)
        (mem_en && mem_rd_wr && (mem_addr == 2'd3)) |=> (address_port_3 == $past(mem_wdata))
    );

endmodule
