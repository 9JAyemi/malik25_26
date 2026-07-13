
module clock_gate(CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output reg ENCLK;

  always @(posedge CLK) begin
    if (EN) ENCLK <= TE;
    else ENCLK <= 0;
  end

endmodule