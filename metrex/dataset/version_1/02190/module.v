
module blk_mem_gen_0blk_mem_gen_v8_2_synth
  (
    output [63:0] doutb,
    input enb,
    input clkb,
    input wea,
    input clka,
    input [8:0] addrb,
    input [8:0] addra,
    input [63:0] dina
  );

  parameter ADDR_WIDTH = 9;
  parameter DATA_WIDTH = 64;
  parameter DEPTH = 2 ** ADDR_WIDTH;

  // Internal wires
  reg  [DATA_WIDTH-1:0] mem [DEPTH-1:0];
  wire [ADDR_WIDTH-1:0] addr;
  reg  [DATA_WIDTH-1:0] data;

  // Address decoding
  assign addr = (clka) ? addra : addrb;

  // Read/Write operations
  always @(posedge clkb) begin
    if (enb) begin
      if (wea) begin // Write operation
        mem[addr] <= dina;
      end else begin // Read operation
        data <= mem[addr];
      end
    end
  end

  assign doutb = data;

endmodule
