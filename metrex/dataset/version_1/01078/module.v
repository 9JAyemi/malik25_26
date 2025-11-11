module block_memory_generator (
  input ENA,
  input clka,
  input ENB,
  input clkb,
  input [9:0] addra,
  input [9:0] addrb,
  input  dina,
  output reg  DOUTB
);

  reg mem [0:1023]; // 2^16 bits of memory

  always @(posedge clka) begin
    if (ENA) begin
      mem[addra] <= dina;
    end
  end

  always @(posedge clkb) begin
    if (ENB) begin
      DOUTB <= mem[addrb];
    end
  end

endmodule