module memory (remapping_memory, full, rd_data, rd_clk, rd_en, rd_addr, reset);

  parameter RD_DATA_WIDTH = 1;
  parameter RD_ADDR_WIDTH = 2;
  parameter MEM_DEPTH = 4;
  
  input wire [MEM_DEPTH-1:0] remapping_memory;
  input wire full;
  output reg [RD_DATA_WIDTH-1:0] rd_data;
  input wire rd_clk, rd_en;
  input wire [RD_ADDR_WIDTH-1:0] rd_addr;
  input wire reset;
  
  reg [RD_DATA_WIDTH-1:0] memory [0:MEM_DEPTH-1];
  integer i;
  
  always @(posedge full, posedge reset) begin
    if(reset) begin
      for(i=0; i<MEM_DEPTH; i=i+1) begin
        memory[i] <= 0;
      end
    end else begin
      for(i=0; i<MEM_DEPTH; i=i+1) begin
        memory[i] <= remapping_memory[i];
      end
    end
  end
  
  always @(posedge rd_clk, posedge reset) begin
    if(reset) begin
      rd_data <= 0;
    end else begin
      if(rd_en) begin
        rd_data <= memory[rd_addr];
      end
    end
  end
  
endmodule