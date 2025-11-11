module fifo_buffer (
  input clk,
  input fifo_rd,
  input rst_n,
  output fifo_EF,
  output reg [7:0] fifo_rdata,
  output rfifo_full,
  output reg [5:0] rfifo_used
);

  // Define FIFO buffer parameters
  parameter DEPTH = 64;
  parameter WIDTH = 8;

  // Define FIFO buffer memory
  reg [WIDTH-1:0] fifo_mem [0:DEPTH-1];
  reg [6:0] write_ptr;
  reg [6:0] read_ptr;
  reg [6:0] used_entries;
  wire fifo_empty = (used_entries == 0);
  wire fifo_full = (used_entries == DEPTH);

  // Define FIFO buffer read logic
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      read_ptr <= 7'b0;
      fifo_rdata <= 8'b0;
      rfifo_used <= 6'b0;
    end
    else if (fifo_rd && !fifo_empty) begin
      fifo_rdata <= fifo_mem[read_ptr];
      read_ptr <= read_ptr + 1;
      rfifo_used <= used_entries - 1;
    end
  end

  // Define FIFO buffer write logic
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      write_ptr <= 7'b0;
      used_entries <= 6'b0;
    end
    else if (!fifo_full) begin
      fifo_mem[write_ptr] <= fifo_rdata;
      write_ptr <= write_ptr + 1;
      used_entries <= used_entries + 1;
    end
  end

  // Define FIFO buffer status outputs
  assign fifo_EF = fifo_empty;
  assign rfifo_full = fifo_full;

endmodule