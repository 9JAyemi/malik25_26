
module tone_generator (
  input clk, // clock signal
  input rst, // reset signal
  input [1:0] type, // type of waveform to generate
  input [15:0] freq, // frequency of waveform
  output reg [7:0] waveform // generated waveform
);

  reg [7:0] dtmf_waveform [0:15];
  reg [15:0] sine_counter = 0;
  reg [15:0] square_counter = 0;
  reg [7:0] sine_waveform = 0;
  reg [7:0] square_waveform = 0;
  reg [7:0] tmp7;

  // DTMF waveform lookup table
  initial begin
    dtmf_waveform[0] = 8'b00000000;
    dtmf_waveform[1] = 8'b00000001;
    dtmf_waveform[2] = 8'b00000010;
    dtmf_waveform[3] = 8'b00000011;
    dtmf_waveform[4] = 8'b00000100;
    dtmf_waveform[5] = 8'b00000101;
    dtmf_waveform[6] = 8'b00000110;
    dtmf_waveform[7] = 8'b00000111;
    dtmf_waveform[8] = 8'b00001000;
    dtmf_waveform[9] = 8'b00001001;
    dtmf_waveform[10] = 8'b00001010;
    dtmf_waveform[11] = 8'b00001011;
    dtmf_waveform[12] = 8'b00001100;
    dtmf_waveform[13] = 8'b00001101;
    dtmf_waveform[14] = 8'b00001110;
    dtmf_waveform[15] = 8'b00001111;
  end

  // DTMF waveform generation
  always @ (posedge clk, posedge rst) begin
    if (rst) begin
      waveform <= 8'b00000000;
    end else begin
      if (type == 2'b00) begin // DTMF
        waveform <= dtmf_waveform[freq];
      end else if (type == 2'b01) begin // sine wave
        sine_counter <= sine_counter + freq;
        sine_waveform <= $signed(8'b10000000) >> (sine_counter / 32768);
      end else begin // square wave
        square_counter <= square_counter + freq;
        if (square_counter >= 16384) begin
          square_waveform <= 8'b11111111;
        end else begin
          square_waveform <= 8'b00000000;
        end
      end
      waveform <= (type == 2'b00) ? dtmf_waveform[freq] : ((type == 2'b01) ? sine_waveform : square_waveform);
    end
  end

endmodule