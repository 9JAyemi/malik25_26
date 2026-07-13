module d_ff(D, CLK, Q, QN);
  parameter GATE_DELAY = 5; // propagation delay in ns
  parameter SETUP_TIME = 2; // setup time in ns

  output reg Q, QN;
  input D, CLK;
  
  wire G;
  assign G = (CLK & ~D);

  always @(posedge CLK) begin
    Q <= D;
    QN <= ~D;
  end

endmodule