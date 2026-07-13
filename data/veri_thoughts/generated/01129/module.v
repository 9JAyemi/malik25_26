module clock_gate (CLK, EN, TE, ENCLK);

  input CLK, EN, TE;
  output reg ENCLK;

  always @ (posedge CLK) begin
    if (EN && !TE) begin
      ENCLK <= CLK;
    end else begin
      ENCLK <= 1'b0;
    end
  end

endmodule