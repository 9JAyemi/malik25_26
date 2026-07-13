
module myClockGate (input CLK, input EN, input TE, output ENCLK);
  wire Q = TE ? CLK : (EN ? Q_reg : 1'b0);
  reg Q_reg;

  always @(posedge CLK) begin
    if (EN) begin
      Q_reg <= Q;
    end
  end

  assign ENCLK = Q;
endmodule