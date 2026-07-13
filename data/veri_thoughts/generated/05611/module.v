module d_ff_set(
  input  wire D,
  input  wire SET_B,
  input  wire CLK,
  output reg Q
);

  always @(posedge CLK) begin
    if (SET_B) begin
      Q <= 1;
    end else begin
      Q <= D;
    end
  end

endmodule