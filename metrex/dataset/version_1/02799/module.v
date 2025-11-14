module blk_mem_gen_0blk_mem_gen_top
   (doutb,
    enb,
    clkb,
    wea,
    clka,
    addrb,
    addra,
    dina);
  output [63:0]doutb;
  input enb;
  input clkb;
  input [0:0]wea;
  input clka;
  input [8:0]addrb;
  input [8:0]addra;
  input [63:0]dina;

  reg [63:0] memory [0:511];  // 512 locations, 64 bits each
  wire [63:0]doutb;
  wire [8:0]addra;
  wire [8:0]addrb;
  wire clka;
  wire clkb;
  wire enb;
  wire [0:0]wea;

  assign addra = addra[8:0];  // truncate to 9 bits
  assign addrb = addrb[8:0];  // truncate to 9 bits

  always @ (posedge clka) begin
    if (enb && wea == 1'b1) begin
      memory[addra] <= dina;
    end
  end

  assign doutb = memory[addrb];

endmodule