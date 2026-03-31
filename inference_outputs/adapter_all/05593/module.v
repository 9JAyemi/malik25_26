module binary_counter(
  input E,
  input s_aclk,
  input AR,
  output reg [3:0] Q
);

  always @(posedge s_aclk) begin
    if (AR) begin
      Q <= 4'b0;
    end else if (E) begin
      Q <= (Q == 4'b1111) ? 4'b0 : Q + 1;
    end
  end

endmodule