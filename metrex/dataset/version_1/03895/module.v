
module chatgpt_generate_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [31:0]   Q
);

  reg [31:0] lfsr_reg;

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      lfsr_reg <= 32'h00000001;
      Q <= 4'b0001;
    end
    else begin
      lfsr_reg <= { lfsr_reg[30:0], lfsr_reg[31] ^ lfsr_reg[28] };
      Q <= lfsr_reg[3:0];
    end
  end

endmodule