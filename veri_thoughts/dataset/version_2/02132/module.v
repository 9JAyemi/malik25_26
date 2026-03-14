module Johnson_counter(
  input                clk,
  input                rst_n,
  output reg  [7:0]    Q
);

  reg [7:0] shift_reg;
  
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      shift_reg <= 8'b00000000;
      Q <= 4'b0000;
    end
    else begin
      shift_reg <= {shift_reg[6:0], shift_reg[7]};
      case (shift_reg)
        8'b00000000: Q <= 4'b0000;
        8'b10000000: Q <= 4'b0001;
        8'b11000000: Q <= 4'b0011;
        8'b11100000: Q <= 4'b0111;
        8'b11110000: Q <= 4'b1111;
        8'b11111000: Q <= 4'b1110;
        8'b11111100: Q <= 4'b1100;
        8'b11111110: Q <= 4'b1000;
        8'b11111111: Q <= 4'b0000;
        8'b01111111: Q <= 4'b0001;
        8'b00111111: Q <= 4'b0011;
        8'b00011111: Q <= 4'b0111;
        8'b00001111: Q <= 4'b1111;
        8'b00000111: Q <= 4'b1110;
        8'b00000011: Q <= 4'b1100;
        8'b00000001: Q <= 4'b1000;
      endcase
    end
  end

endmodule