
module clock_gate_64bit_reg (
  input CLK,
  input EN,
  input TE,
  output reg ENCLK
);

  localparam TLATNTSCAX2TS = 0;

  always @(posedge CLK) begin
    if (EN & ~TE) begin
      ENCLK <= 1;
    end else begin
      ENCLK <= 0;
    end
  end

endmodule