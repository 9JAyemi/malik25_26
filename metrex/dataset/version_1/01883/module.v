module pwm_generator (
  input clk,
  input rst,
  output reg pwm_out
);

reg [1:0] counter = 2'b0;

always @(posedge clk) begin
  if (rst) begin
    pwm_out <= 0;
    counter <= 2'b0;
  end else begin
    if (counter == 2'b11) begin
      pwm_out <= 1;
      counter <= 2'b0;
    end else begin
      pwm_out <= 0;
      counter <= counter + 1;
    end
  end
end

endmodule