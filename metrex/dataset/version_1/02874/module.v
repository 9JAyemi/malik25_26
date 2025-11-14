
module tone_generator (
  input clk,
  input reset,
  input [1:0] mode,
  input [7:0] freq,
  output reg signed [N-1:0] tone
);

parameter fs = 100000; // sampling frequency
parameter N = 8; // number of bits used to represent the amplitude of the tone signal

reg [31:0] phase_acc;
reg [31:0] phase_inc;

always @ (posedge clk) begin
  if (reset) begin
    phase_acc <= 0;
    tone <= 0;
  end else begin
    phase_acc <= phase_acc + phase_inc;
    case (mode)
      2'b00: begin // DTMF
        case (freq)
          8'h11: phase_inc <= 32'd3486784;
          8'h12: phase_inc <= 32'd3853932;
          8'h13: phase_inc <= 32'd4261416;
          8'h14: phase_inc <= 32'd4706164;
          8'h21: phase_inc <= 32'd6048840;
          8'h22: phase_inc <= 32'd6684096;
          8'h23: phase_inc <= 32'd7389128;
          8'h24: phase_inc <= 32'd8165376;
        endcase
        tone <= $signed({{(N-1){phase_acc[31]}}, (phase_acc[31:0]) * 2**(N-1)})>>>0;
      end
      2'b01: begin // sine wave
        phase_inc <= 32'd1572864 * freq;
        tone <= $signed({{(N-1){phase_acc[31]}}, (phase_acc[31:0]) * 2**(N-1)})>>>0;
      end
      2'b10: begin // square wave
        phase_inc <= 32'd1572864 * freq;
        if (phase_acc[31]) begin
          tone <= (N-1);
        end else begin
          tone <= -(N-1);
        end
      end
    endcase
  end
end

endmodule