

module ad_mem (

  clka,
  wea,
  addra,
  dina,

  clkb,
  addrb,
  doutb);

  parameter       DATA_WIDTH = 16;
  parameter       ADDRESS_WIDTH =  5;
  localparam      DW = DATA_WIDTH - 1;
  localparam      AW = ADDRESS_WIDTH - 1;

  input           clka;
  input           wea;
  input   [AW:0]  addra;
  input   [DW:0]  dina;

  input           clkb;
  input   [AW:0]  addrb;
  output  [DW:0]  doutb;

  reg     [DW:0]  m_ram[0:((2**ADDRESS_WIDTH)-1)];
  reg     [DW:0]  doutb;

  always @(posedge clka) begin
    if (wea == 1'b1) begin
      m_ram[addra] <= dina;
    end
  end

  always @(posedge clkb) begin
    doutb <= m_ram[addrb];
  end

endmodule

