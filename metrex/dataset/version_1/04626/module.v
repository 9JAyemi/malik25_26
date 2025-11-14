
module top_module (
  input clk,
  input reset,
  input [7:0] in,
  input [4:0] shift_amount,
  output [7:0] shifted_out,
  output zero_flag
);

  // Priority Encoder module
  wire [2:0] pe_out;
  priority_encoder pe (
    .in(in),
    .out(pe_out)
  );

  // Barrel Shifter module
  barrel_shifter bs (
    .in(in),
    .shift_amount(shift_amount),
    .out(shifted_out)
  );

  // Zero Flag module
  assign zero_flag = (shifted_out == 0);

  // Internal register for priority encoder output
  reg [2:0] pe_out_internal;

  // Reset logic
  always @(posedge clk) begin
    if (reset) begin
      pe_out_internal <= 3'b0;
    end else begin
      pe_out_internal <= pe_out;
    end
  end

endmodule
module priority_encoder (
  input [7:0] in,
  output [2:0] out
);

  assign out = (in[0]) ? 3'b001 :
               (in[1]) ? 3'b010 :
               (in[2]) ? 3'b011 :
               (in[3]) ? 3'b100 :
               (in[4]) ? 3'b101 :
               (in[5]) ? 3'b110 :
               (in[6]) ? 3'b111 :
               3'b000;

endmodule
module barrel_shifter (
  input [7:0] in,
  input [4:0] shift_amount,
  output reg [7:0] out
);

  always @(*) begin
    case (shift_amount)
      5'b00000: out = in;
      5'b00001: out = {in[6:0], 1'b0};
      5'b00010: out = {in[5:0], 2'b00};
      5'b00011: out = {in[4:0], 3'b000};
      5'b00100: out = {in[3:0], 4'b0000};
      5'b00101: out = {in[2:0], 5'b00000};
      5'b00110: out = {in[1:0], 6'b000000};
      5'b00111: out = {in[0], 7'b0000000};
      default: out = 8'b0;
    endcase
  end

endmodule