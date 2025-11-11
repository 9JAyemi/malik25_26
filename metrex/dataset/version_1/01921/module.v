module motor_control (
  input clk,
  input rst,
  input pwm_in,
  input dir,
  input [7:0] speed,
  output pwm_out,
  output [1:0] motor_a_b
);

  reg [7:0] counter;
  reg pwm_out;
  reg [1:0] motor_a_b;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      counter <= 8'd0;
      pwm_out <= 1'b0;
      motor_a_b <= 2'b00;
    end else begin
      counter <= counter + 1;
      if (counter >= speed) begin
        counter <= 8'd0;
        pwm_out <= ~pwm_out;
      end
      if (dir) begin
        motor_a_b <= 2'b10;
      end else begin
        motor_a_b <= 2'b01;
      end
    end
  end

endmodule