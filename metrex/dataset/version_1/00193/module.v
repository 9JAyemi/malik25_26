module wifi_tx (
  input [7:0] data_in,
  input clk,
  output reg [15:0] mod_signal_out
);

  reg [3:0] I, Q;
  reg [1:0] phase;
  
  always @(*) begin
    case(data_in)
      8'b00000000: begin I = 4'b0000; Q = 4'b0000; end
      8'b00000001: begin I = 4'b0000; Q = 4'b0001; end
      8'b00000010: begin I = 4'b0000; Q = 4'b0010; end
      8'b00000011: begin I = 4'b0000; Q = 4'b0011; end
      8'b00000100: begin I = 4'b0000; Q = 4'b0100; end
      8'b00000101: begin I = 4'b0000; Q = 4'b0101; end
      8'b00000110: begin I = 4'b0000; Q = 4'b0110; end
      8'b00000111: begin I = 4'b0000; Q = 4'b0111; end
      8'b00001000: begin I = 4'b0001; Q = 4'b0000; end
      8'b00001001: begin I = 4'b0001; Q = 4'b0001; end
      8'b00001010: begin I = 4'b0001; Q = 4'b0010; end
      8'b00001011: begin I = 4'b0001; Q = 4'b0011; end
      8'b00001100: begin I = 4'b0001; Q = 4'b0100; end
      8'b00001101: begin I = 4'b0001; Q = 4'b0101; end
      8'b00001110: begin I = 4'b0001; Q = 4'b0110; end
      8'b00001111: begin I = 4'b0001; Q = 4'b0111; end
      8'b00010000: begin I = 4'b0010; Q = 4'b0000; end
      8'b00010001: begin I = 4'b0010; Q = 4'b0001; end
      8'b00010010: begin I = 4'b0010; Q = 4'b0010; end
      8'b00010011: begin I = 4'b0010; Q = 4'b0011; end
      8'b00010100: begin I = 4'b0010; Q = 4'b0100; end
      8'b00010101: begin I = 4'b0010; Q = 4'b0101; end
      8'b00010110: begin I = 4'b0010; Q = 4'b0110; end
      8'b00010111: begin I = 4'b0010; Q = 4'b0111; end
      8'b00011000: begin I = 4'b0011; Q = 4'b0000; end
      8'b00011001: begin I = 4'b0011; Q = 4'b0001; end
      8'b00011010: begin I = 4'b0011; Q = 4'b0010; end
      8'b00011011: begin I = 4'b0011; Q = 4'b0011; end
      8'b00011100: begin I = 4'b0011; Q = 4'b0100; end
      8'b00011101: begin I = 4'b0011; Q = 4'b0101; end
      8'b00011110: begin I = 4'b0011; Q = 4'b0110; end
      8'b00011111: begin I = 4'b0011; Q = 4'b0111; end
      8'b00100000: begin I = 4'b0100; Q = 4'b0000; end
      8'b00100001: begin I = 4'b0100; Q = 4'b0001; end
      8'b00100010: begin I = 4'b0100; Q = 4'b0010; end
      8'b00100011: begin I = 4'b0100; Q = 4'b0011; end
      8'b00100100: begin I = 4'b0100; Q = 4'b0100; end
      8'b00100101: begin I = 4'b0100; Q = 4'b0101; end
      8'b00100110: begin I = 4'b0100; Q = 4'b0110; end
      8'b00100111: begin I = 4'b0100; Q = 4'b0111; end
      8'b00101000: begin I = 4'b0101; Q = 4'b0000; end
      8'b00101001: begin I = 4'b0101; Q = 4'b0001; end
      8'b00101010: begin I = 4'b0101; Q = 4'b0010; end
      8'b00101011: begin I = 4'b0101; Q = 4'b0011; end
      8'b00101100: begin I = 4'b0101; Q = 4'b0100; end
      8'b00101101: begin I = 4'b0101; Q = 4'b0101; end
      8'b00101110: begin I = 4'b0101; Q = 4'b0110; end
      8'b00101111: begin I = 4'b0101; Q = 4'b0111; end
      8'b00110000: begin I = 4'b0110; Q = 4'b0000; end
      8'b00110001: begin I = 4'b0110; Q = 4'b0001; end
      8'b00110010: begin I = 4'b0110; Q = 4'b0010; end
      8'b00110011: begin I = 4'b0110; Q = 4'b0011; end
      8'b00110100: begin I = 4'b0110; Q = 4'b0100; end
      8'b00110101: begin I = 4'b0110; Q = 4'b0101; end
      8'b00110110: begin I = 4'b0110; Q = 4'b0110; end
      8'b00110111: begin I = 4'b0110; Q = 4'b0111; end
      8'b00111000: begin I = 4'b0111; Q = 4'b0000; end
      8'b00111001: begin I = 4'b0111; Q = 4'b0001; end
      8'b00111010: begin I = 4'b0111; Q = 4'b0010; end
      8'b00111011: begin I = 4'b0111; Q = 4'b0011; end
      8'b00111100: begin I = 4'b0111; Q = 4'b0100; end
      8'b00111101: begin I = 4'b0111; Q = 4'b0101; end
      8'b00111110: begin I = 4'b0111; Q = 4'b0110; end
      8'b00111111: begin I = 4'b0111; Q = 4'b0111; end
      default: begin I = 4'b0000; Q = 4'b0000; end
    endcase
  end
  
  always @(posedge clk) begin
    case(phase)
      2'b00: begin mod_signal_out = {I, Q}; phase <= 2'b01; end
      2'b01: begin mod_signal_out = {I, -Q}; phase <= 2'b10; end
      2'b10: begin mod_signal_out = {-I, -Q}; phase <= 2'b11; end
      2'b11: begin mod_signal_out = {-I, Q}; phase <= 2'b00; end
    endcase
  end
  
endmodule