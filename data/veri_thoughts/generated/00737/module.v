module shift_register(
  input CLK,
  input LOAD,
  input SHIFT,
  input [3:0] D,
  output reg [3:0] Q
);

  always @(posedge CLK) begin
    if (LOAD) begin
      Q <= D;
    end else if (SHIFT) begin
      Q <= {Q[2:0], 1'b0};
    end
  end

endmodule