
module memory_interface(clka, wea, addra, dina, douta);
  parameter MEM_SIZE = 2**8; // 14-bit address gives 2^14 memory locations
  parameter MEM_WIDTH = 12; // each memory location holds 1 byte of data
  reg [MEM_WIDTH-1:0] mem [0:MEM_SIZE-1]; // declare memory array

  input clka;
  input  wea;
  input [7:0] addra;
  input [MEM_WIDTH-1:0] dina;
  output reg [MEM_WIDTH-1:0] douta;

  always @(posedge clka) begin
    if (wea == 1'b1) begin // write to memory
      mem[addra] <= dina;
    end
    douta <= mem[addra];
  end

endmodule