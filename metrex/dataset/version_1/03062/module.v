module tone_detection_generation (
  input clk,
  input reset,
  input in,
  input freq,
  output reg det,
  output reg gen
);

  reg [31:0] phase_acc = 0;
  reg [31:0] phase_inc = 0;
  reg [31:0] tone = 0;
  reg [31:0] threshold = 0;
  reg [31:0] sample_count = 0;
  reg [31:0] sample_rate = 48000;
  reg [31:0] sample_period = 0;
  reg [31:0] sample_threshold = 0;
  reg det_flag = 0;
  reg gen_flag = 0;
  reg gen_en = 0;
  reg [31:0] in_sample = 0;
  reg [31:0] gen_sample = 0;

  always @ (posedge clk) begin
    if (reset) begin
      phase_acc <= 0;
      phase_inc <= 0;
      tone <= 0;
      threshold <= 0;
      sample_count <= 0;
      sample_period <= 0;
      sample_threshold <= 0;
      det_flag <= 0;
      gen_flag <= 0;
      gen_en <= 0;
    end else begin
      in_sample <= in;

      if (freq > 0) begin
        phase_inc <= ((freq << 32) / sample_rate);
        tone <= $unsigned($signed(phase_acc[31]) ? ~32'h0 : 32'h0);
        phase_acc <= phase_acc + phase_inc;
      end else begin
        phase_acc <= 0;
        tone <= 0;
      end

      if (det_flag) begin
        if (in_sample > threshold) begin
          sample_count <= sample_count + 1;
        end else begin
          sample_count <= 0;
        end

        if (sample_count >= sample_period) begin
          det_flag <= 0;
          det <= 1;
        end else begin
          det <= 0;
        end
      end else begin
        if (in_sample > threshold) begin
          sample_count <= sample_count + 1;
        end else begin
          sample_count <= 0;
        end

        if (sample_count >= sample_threshold) begin
          det_flag <= 1;
          sample_period <= sample_count;
          sample_count <= 0;
          threshold <= in_sample;
        end
      end

      if (gen_flag) begin
        if (gen_en) begin
          gen_sample <= tone;
        end else begin
          gen_sample <= 0;
        end
      end else begin
        gen_sample <= 0;
      end

      if (freq > 0) begin
        gen_en <= 1;
      end else begin
        gen_en <= 0;
      end

      if (gen_en) begin
        tone <= $unsigned($signed(phase_acc[31]) ? ~32'h0 : 32'h0);
        phase_acc <= phase_acc + phase_inc;
      end else begin
        tone <= 0;
        phase_acc <= 0;
      end

      if (gen_en) begin
        gen_flag <= 1;
        gen <= gen_sample;
      end else begin
        gen_flag <= 0;
        gen <= 0;
      end
    end
  end
endmodule