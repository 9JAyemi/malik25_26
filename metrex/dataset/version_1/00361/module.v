
module mem_test (
  input clk,
  input rst,
  input [7:0] addr,
  input [7:0] din,
  input mem_en,
  output [7:0] dout,
  output error
);

  // Define RAM module
  reg [7:0] mem [0:255];

  // Define internal signals
  reg [7:0] read_data;
  reg write_en;
  reg read_en;
  reg [7:0] error_addr;
  wire [7:0] mem_addr;

  // Assign memory address
  assign mem_addr = addr;

  // Write operation
  always @(posedge clk, posedge rst) begin
    if (rst) begin
      write_en <= 0;
      error_addr <= 0;
    end else begin
      if (mem_en) begin
        write_en <= 1;
        mem[addr] <= din;
      end else begin
        write_en <= 0;
      end
    end
  end

  // Read operation
  always @(posedge clk, posedge rst) begin
    if (rst) begin
      read_en <= 0;
      read_data <= 0;
    end else begin
      if (mem_en) begin
        read_en <= 1;
        read_data <= mem[addr];
      end else begin
        read_en <= 0;
      end
    end
  end

  // Error detection
  wire error_wire;
  assign error_wire = (write_en && read_en && (din != read_data));
  reg error_reg;
  always @(posedge clk, posedge rst) begin
    if (rst) begin
      error_reg <= 0;
    end else begin
      if (mem_en) begin
        if (error_wire) begin
          error_reg <= 1;
          error_addr <= addr;
        end else begin
          error_reg <= 0;
        end
      end else begin
        error_reg <= 0;
      end
    end
  end

  // Assign outputs
  assign dout = read_data;
  assign error = error_reg;

endmodule
