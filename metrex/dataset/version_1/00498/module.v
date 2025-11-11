
module fifo_memory #
  (
    parameter DW       = 8,         
    parameter DEPTH    = 8,         
    parameter REG      = 0,         
    parameter AW       = $clog2(DEPTH),
    parameter PROGFULL = DEPTH-1
  ) 
  (
    input        clk,      
    input        nreset,   
    input        clear,    
    input [DW-1:0]  din,   
    input        wr_en,    
    output       full,     
    output       almost_full, 
    input        rd_en,    
    output [DW-1:0] dout,  
    output       empty,    
    output reg [AW-1:0] rd_count 
  );

  reg [AW-1:0]          wr_addr;
  reg [AW-1:0]          rd_addr;
  wire                fifo_read;
  wire                fifo_write;
  wire                ptr_match;
  wire                fifo_empty;

  assign fifo_read   = rd_en & ~empty;
  assign fifo_write  = wr_en & ~full;
  assign almost_full = (rd_count == PROGFULL);
  assign ptr_match   = (wr_addr == rd_addr);
  assign full        = ptr_match & (wr_addr[AW-1]!=rd_addr[AW-1]);
  assign fifo_empty  = ptr_match & (wr_addr[AW-1]==rd_addr[AW-1]);

  always @ (posedge clk or negedge nreset) begin
    if(~nreset) begin	   
      wr_addr <= 0;
      rd_addr <= 0;
      rd_count <= 0;
    end else if(clear) begin	   
      wr_addr <= 0;
      rd_addr <= 0;
      rd_count <= 0;
    end else if(fifo_write & fifo_read) begin
      wr_addr <= wr_addr + 1;
      rd_addr <= rd_addr + 1;	      
    end else if(fifo_write) begin
      wr_addr <= wr_addr + 1;
      rd_count <= rd_count + 1;	
    end else if(fifo_read) begin	      
      rd_addr <= rd_addr + 1;
      rd_count <= rd_count - 1;
    end
  end

  reg empty_reg;	   
  always @ (posedge clk) begin
    empty_reg <= fifo_empty;
  end

  assign empty = (REG==1) ? empty_reg : fifo_empty;

  dual_port_ram #(
    .DATA_WIDTH(DW),
    .ADDR_WIDTH(AW)
  ) ram(
        .we(fifo_write),
        .clk(clk),
        .addr1(wr_addr),
        .addr2(rd_addr),
        .din(din),
        .dout(dout)
    );

endmodule
module dual_port_ram #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
  ) (
    input        clk,
    input        we,
    input [ADDR_WIDTH-1:0]  addr1,
    input [ADDR_WIDTH-1:0]  addr2,
    input [DATA_WIDTH-1:0]  din,
    output [DATA_WIDTH-1:0]  dout
  );
   reg [DATA_WIDTH-1:0] ram [0:2**ADDR_WIDTH-1];
   
   assign dout = (addr2 == addr1) ? din : ram[addr2];
   
   always @(posedge clk)
     if (we)
       ram[addr1] <= din;
endmodule