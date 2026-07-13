
module tone_generator (
  input clk,
  input rst,
  input [1:0] tone,
  output audio_out
);

parameter f_clk = 50_000_000; // frequency of the clock signal
parameter f_tone = 440; // frequency of the selected tone (default: A4)
parameter t_duration = 1; // duration of the tone in seconds (default: 1 second)

reg [31:0] tone_counter = 0;
reg [31:0] tone_duration = 0;
reg [31:0] sample_counter = 0;
reg [31:0] sample_period = 0;
reg [1:0] tone_type = 2'b00; // default: sine wave

wire tone_signal;

// DTMF tone generation
always @ (posedge clk) begin
  if (rst) begin
    tone_counter <= 0;
    tone_duration <= 0;
    sample_counter <= 0;
    sample_period <= 0;
    tone_type <= 2'b00;
  end else begin
    // Check if tone is selected
    if (tone != 2'b00) begin
      // A new tone is selected
      if (tone != tone_type) begin
        tone_counter <= 0;
        tone_duration <= t_duration * f_clk;
        sample_counter <= 0;
        sample_period <= f_clk / f_tone;
        tone_type <= tone;
      end else begin // Same tone is selected
        // Check if tone duration is reached
        if (tone_counter >= tone_duration) begin
          tone_counter <= 0;
          tone_duration <= 0;
          sample_counter <= 0;
          sample_period <= 0;
          tone_type <= 2'b00;
        end else begin
          tone_counter <= tone_counter + 1;
          sample_counter <= sample_counter + 1;
          // Check if a new sample is needed
          if (sample_counter >= sample_period) begin
            sample_counter <= 0;
          end
        end
      end
    end else begin // No tone is selected
      tone_counter <= 0;
      tone_duration <= 0;
      sample_counter <= 0;
      sample_period <= 0;
      tone_type <= 2'b00;
    end
  end
end

// Sine wave generation
assign tone_signal = (tone_counter >= (f_clk / (2 * f_tone))) ? 1'b1 : 1'b0;

// Audio output
assign audio_out = tone_signal;

endmodule