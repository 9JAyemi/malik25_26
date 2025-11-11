
module dct_processor (
  input clk,
  input [29:0] dct_buffer,
  input [3:0] dct_count,
  input test_ending,
  input test_has_ended,
  output [15:0] current_coefficient,
  output [3:0] total_coefficients
);

  reg [29:0] dct_buffer_reg;
  reg [3:0] dct_count_reg;
  reg [15:0] current_coefficient_reg;
  reg [3:0] total_coefficients_reg;
  reg processing;
  
  always @(posedge clk) begin
    if (test_ending == 1) begin
      processing <= 0;
    end else if (processing == 1 && dct_count_reg == 0) begin
      processing <= 0;
    end else if (processing == 0 && dct_count_reg > 0) begin
      processing <= 1;
    end
  end
  
  always @(posedge clk) begin
    if (processing == 1) begin
      current_coefficient_reg <= dct_buffer_reg[15:0];
      dct_buffer_reg <= {dct_buffer_reg[14:0], 1'b0};
      dct_count_reg <= dct_count_reg - 1;
      if (dct_count_reg == 0) begin
        total_coefficients_reg <= total_coefficients_reg + 1;
      end
    end else begin
      current_coefficient_reg <= 0;
      dct_buffer_reg <= dct_buffer;
      dct_count_reg <= dct_count;
      total_coefficients_reg <= 0;
    end
  end
  
  assign current_coefficient = current_coefficient_reg;
  assign total_coefficients = total_coefficients_reg;
  
endmodule
