
module udp_dff(input D, CLK, CLR, SET, output Q, QN);
  reg Q;

  always @(posedge CLK) begin
    if (CLR)
      Q <= 1'b0;
    else if (SET)
      Q <= 1'b1;
    else
      Q <= D;
  end

  assign QN = ~Q;
endmodule