module clock_gate_d_ff_en_W32_0_6 (
  input CLK, 
  input EN, 
  input TE, 
  input [31:0] DATA, 
  output reg ENCLK
);

  reg D;
  always @(posedge CLK) begin
    if (EN & !TE) begin
      D <= DATA;
    end
  end

  always @(posedge CLK) begin
    if (TE) begin
      ENCLK <= 0;
    end else if (EN) begin
      ENCLK <= CLK;
    end else begin
      ENCLK <= 0;
    end
  end

endmodule