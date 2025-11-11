
module ram_16x1k_sp (
  clka,
  ena,
  wea,
  addra,
  dina,
  douta
);

input clka;
input ena;
input [1 : 0] wea;
input [9 : 0] addra;
input [15 : 0] dina;
output [15 : 0] douta;


reg [15:0] mem[0:16383];

always @(posedge clka) begin
    if (ena) begin
        if (wea == 2'b01) // byte write
            mem[addra][7:0] <= dina[7:0];
        else if (wea == 2'b10) // half-word write
            mem[addra][15:8] <= dina[15:8];
        else if (wea == 2'b11) // word write
            mem[addra] <= dina;
    end
end

assign douta = mem[addra];

endmodule
