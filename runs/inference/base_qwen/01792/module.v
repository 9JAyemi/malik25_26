module port_address_reg
    (
    input  wire clk,                   // System Clock
    input  wire reset_b,               // Active high, asyn reset
    input  wire         mem_en,        // Memory enable
    input  wire         mem_rd_wr,     // Memory read/write
    input  wire [01:00] mem_addr,      // Memory address
    input  wire [07:00] mem_wdata,     // Memory data
    output reg  [07:00] mem_rdata,     // Memory data
    output reg  [07:00] address_port_0,// Port 0 address
    output reg  [07:00] address_port_1,// Port 1 address
    output reg  [07:00] address_port_2,// Port 2 address
    output reg  [07:00] address_port_3 // Port 3 address
    );
    
    always@*
        case(mem_addr)
            2'd0: mem_rdata <= address_port_0;
            2'd1: mem_rdata <= address_port_1;
            2'd2: mem_rdata <= address_port_2;
            2'd3: mem_rdata <= address_port_3;
        endcase
    
    always @(posedge clk or negedge reset_b) begin
            if (~reset_b) begin
                    address_port_0 <= 8'h00;
                    address_port_1 <= 8'h01;
                    address_port_2 <= 8'h02;
                    address_port_3 <= 8'h03;
                end
            else if (mem_en && mem_rd_wr) begin
                    case (mem_addr)
                        2'b00: address_port_0 <= mem_wdata;
                        2'b01: address_port_1 <= mem_wdata;
                        2'b10: address_port_2 <= mem_wdata;
                        2'b11: address_port_3 <= mem_wdata;
                    endcase
                end
        end
endmodule