module add_subtract_display (
  input clk,
  input reset,
  input [3:0] a,
  input [3:0] b,
  input op,
  output reg [6:0] seg
);

  // Adder module
  wire [3:0] add_out;
  adder add_inst (.a(a), .b(b), .sum(add_out));

  // Subtractor module
  wire [3:0] sub_out;
  subtractor sub_inst (.a(a), .b(b), .diff(sub_out));

  // Shift register for adder output
  reg [6:0] add_shift_reg = 7'b0000000;
  always @(posedge clk) begin
    if (reset) begin
      add_shift_reg <= 7'b0000000;
    end else begin
      add_shift_reg <= {add_shift_reg[5:0], add_out[3]};
    end
  end

  // Shift register for subtractor output
  reg [6:0] sub_shift_reg = 7'b0000000;
  always @(posedge clk) begin
    if (reset) begin
      sub_shift_reg <= 7'b0000000;
    end else begin
      sub_shift_reg <= {sub_shift_reg[5:0], sub_out[3]};
    end
  end

  // Output selection logic
  reg [6:0] display_out = 7'b0000000;
  always @(posedge clk) begin
    if (reset) begin
      display_out <= 7'b0000000;
    end else begin
      if (op == 0) begin
        display_out <= add_shift_reg;
      end else begin
        display_out <= sub_shift_reg;
      end
    end
  end

  // 7-segment display decoder
  always @(*) begin
    case (display_out)
      7'b0000000: seg = 7'b1111110; // 0
      7'b0000001: seg = 7'b0110000; // 1
      7'b0000010: seg = 7'b1101101; // 2
      7'b0000011: seg = 7'b1111001; // 3
      7'b0000100: seg = 7'b0110011; // 4
      7'b0000101: seg = 7'b1011011; // 5
      7'b0000110: seg = 7'b1011111; // 6
      7'b0000111: seg = 7'b1110000; // 7
      7'b0001000: seg = 7'b1111111; // 8
      7'b0001001: seg = 7'b1110011; // 9
      default: seg = 7'b0000001; // Error (display "-")
    endcase
  end

endmodule

// Adder module
module adder (
  input [3:0] a,
  input [3:0] b,
  output reg [3:0] sum
);
  always @(*) begin
    sum = a + b;
  end
endmodule

// Subtractor module
module subtractor (
  input [3:0] a,
  input [3:0] b,
  output reg [3:0] diff
);
  always @(*) begin
    diff = a - b;
  end
endmodule