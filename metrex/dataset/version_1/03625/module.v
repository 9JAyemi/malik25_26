
module SSCG (
  input clk_in, // input clock signal
  input clk_en, // SSCG enable signal
  input [31:0] sscg_freq, // frequency deviation parameter
  output clk_out // output clock signal
);

  reg [31:0] fm_accumulator;
  reg [31:0] fm_increment;
  reg [31:0] fm_modulation;
  reg clk_output;

  always @ (posedge clk_in) begin
    if (clk_en) begin
      fm_accumulator <= fm_accumulator + fm_increment;
      fm_modulation <= sscg_freq >> 1; // fix: remove $urandom
      clk_output <= (fm_accumulator + fm_modulation) >> 1;
    end else begin
      clk_output <= clk_in;
    end
  end

  assign clk_out = clk_output;

  parameter PERIOD = (2**32 / 1000) * 100; // 100 kHz

  initial begin
    fm_accumulator <= 0;
    fm_increment <= PERIOD; // 100 kHz
    fm_modulation <= 0;
    clk_output <= 0;
  end

endmodule