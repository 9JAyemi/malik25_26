module clock_gate (
  input CLK,
  input EN,
  input TE,
  output reg ENCLK
);

  always @(posedge CLK) begin
    if (EN == 1'b0) begin
      ENCLK <= 1'b0;
    end else begin
      if (TE == 1'b1) begin
        ENCLK <= CLK;
      end else begin
        ENCLK <= 1'b0;
      end
    end
  end
  
endmodule