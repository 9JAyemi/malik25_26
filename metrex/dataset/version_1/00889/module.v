
module my_memory(
  input clka,
  input [15 : 0] addra,
  output [11 : 0] douta,
  input ena,
  input regcea,
  input wea,
  input [11 : 0] dina,
  input rst
);


reg [11 : 0] mem [256 : 0];

  always @ (posedge clka)
  begin
    if (ena & regcea & wea)
      mem[addra] <= dina;
  end

  assign douta = (ena & regcea) ? mem[addra] : 12'b0;

endmodule