
module IrDA_transmitter (
  input clk,
  input rst,
  input [7:0] data_in,
  output ir_out
);
  reg [7:0] data_reg;
  reg [3:0] pwm_counter;
  reg pwm_out;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      data_reg <= 8'h0;
      pwm_counter <= 4'h0;
      pwm_out <= 1'b0;
    end else begin
      data_reg <= data_in;
      pwm_counter <= pwm_counter + 1;
      pwm_out <= (pwm_counter < data_reg[3:0]) ? 1'b1 : 1'b0;
    end
  end

  assign ir_out = pwm_out;
endmodule
module IrDA_receiver (
  input clk,
  input rst,
  input ir_in,
  output [7:0] data_out
);
  reg [3:0] pwm_counter;
  reg [7:0] data_reg;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      data_reg <= 8'h0;
      pwm_counter <= 4'h0;
    end else begin
      if (ir_in) begin
        pwm_counter <= pwm_counter + 1;
      end else begin
        if (pwm_counter != 4'h0) begin
          data_reg <= {data_reg[6:0], pwm_counter[3]};
          pwm_counter <= 4'h0;
        end
      end
    end
  end

  assign data_out = data_reg;
endmodule