
module fifo_generator
   (DOUTB,
    clk,
    ENB,
    E,
    Q,
    ADDRB,
    ADDRA,
    din);
  output [93:0]DOUTB;
  input clk;
  input ENB;
  input [0:0]E;
  input [0:0]Q;
  input [5:0]ADDRB;
  input [5:0]ADDRA;
  input [93:0]din;

  reg [93:0] mem [255:0];
  integer ii;

  assign ADDRA = ADDRA[5:0];
  assign ADDRB = ADDRB[5:0];

  assign DOUTB = mem[ADDRB];

  always @(posedge clk) begin
    if (E)
      mem[ADDRA] <= din;
  end

  always @(posedge clk) begin
    if (ENB) begin
      if (Q)
        mem[ADDRB] <= mem[ADDRB+1];
      else
        mem[ADDRB] <= mem[ADDRB-1];
    end
  end

endmodule