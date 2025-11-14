
module blk_mem_gen_1blk_mem_gen_prim_wrapper
       (addra,
        addrb,
        clka,
        clkb,
        dina,
        doutb,
        enb,
        wea);

  parameter WIDTH = 32;
  parameter DEPTH = 1024;

  input [WIDTH-1:0] addra;
  input [WIDTH-1:0] addrb;
  input clka;
  input clkb;
  input [WIDTH-1:0] dina;
  output reg [WIDTH-1:0] doutb;
  input enb;
  input wea;

  reg [WIDTH-1:0] mem [0:DEPTH-1];

  integer i;

  always @(posedge clka) begin
    if (enb) begin
        mem[addra] <= dina; 
    end
  end

  always @(posedge clkb) begin
    if (wea) begin
      doutb <= mem[addrb]; 
    end
  end

  initial begin
    for (i = 0; i < DEPTH; i = i + 1) begin
      mem[i] <= 0;
    end
  end

endmodule