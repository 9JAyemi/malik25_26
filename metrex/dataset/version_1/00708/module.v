
module memory_block_generator
   (douta,
    clka,
    addra,
    dina,
    wea);

  output [2:0]douta;
  input clka;
  input [12:0]addra;
  input [2:0]dina;
  input [0:0]wea;

  reg [2:0] mem [0:8191];

  assign douta = (wea) ? dina : mem[addra[12:1]][addra[0]];
  
  always @(posedge clka) begin
    if (wea) begin
      mem[addra[12:1]][addra[0]] <= dina;
    end
  end
endmodule