
module square_wave_gen (
  input clk,
  input freq,
  output reg square_wave
);

  reg [31:0] counter, half_period, clk_period;

  always @(posedge clk) begin
    if (counter == half_period) begin
      square_wave <= ~square_wave;
      counter <= 0;
    end else begin
      counter <= counter + 1'b1;
    end
  end

  always @(posedge clk) begin
    clk_period <= (clk_period / freq) ? (clk_period / freq) : 1'b0;
    half_period <= clk_period / 2;
  end

endmodule