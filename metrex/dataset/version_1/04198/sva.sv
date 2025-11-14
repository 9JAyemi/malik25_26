// SVA for apu_mixer
// Bind this file to the DUT:
// bind apu_mixer apu_mixer_sva u_apu_mixer_sva(.*);

module apu_mixer_sva
(
  input  wire       clk_in,
  input  wire       rst_in,
  input  wire [3:0] mute_in,
  input  wire [3:0] pulse0_in,
  input  wire [3:0] pulse1_in,
  input  wire [3:0] triangle_in,
  input  wire [3:0] noise_in,
  input  wire       audio_out,

  input  wire [3:0] pulse0,
  input  wire [3:0] pulse1,
  input  wire [3:0] triangle,
  input  wire [3:0] noise,

  input  wire [4:0] pulse_in_total,
  input  wire [5:0] pulse_out,

  input  wire [6:0] tnd_in_total,
  input  wire [5:0] tnd_out,

  input  wire [5:0] mixed_out,

  input  wire [5:0] q_pwm_cnt,
  input  wire [5:0] d_pwm_cnt
);

  default clocking cb @(posedge clk_in); endclocking
  default disable iff (rst_in);

  // Reference LUTs for concise functional checks
  localparam logic [5:0] P_LUT [0:30] = '{
    6'h00,6'h01,6'h01,6'h02,6'h03,6'h03,6'h04,6'h05,
    6'h05,6'h06,6'h07,6'h07,6'h08,6'h08,6'h09,6'h09,
    6'h0A,6'h0A,6'h0B,6'h0B,6'h0C,6'h0C,6'h0D,6'h0D,
    6'h0E,6'h0E,6'h0F,6'h0F,6'h0F,6'h10,6'h10
  };

  localparam logic [5:0] T_LUT [0:75] = '{
    6'h00,6'h01,6'h01,6'h02,6'h03,6'h03,6'h04,6'h05,
    6'h05,6'h06,6'h07,6'h07,6'h08,6'h08,6'h09,6'h09,
    6'h0A,6'h0A,6'h0B,6'h0B,6'h0C,6'h0C,6'h0D,6'h0D,
    6'h0E,6'h0E,6'h0F,6'h0F,6'h0F,6'h10,6'h10,6'h11,
    6'h11,6'h11,6'h12,6'h12,6'h12,6'h13,6'h13,6'h14,
    6'h14,6'h14,6'h15,6'h15,6'h15,6'h15,6'h16,6'h16,
    6'h16,6'h17,6'h17,6'h17,6'h17,6'h18,6'h18,6'h18,
    6'h19,6'h19,6'h19,6'h19,6'h1A,6'h1A,6'h1A,6'h1A,
    6'h1B,6'h1B,6'h1B,6'h1B,6'h1B,6'h1C,6'h1C,6'h1C,
    6'h1C,6'h1C,6'h1D,6'h1D
  };

  // Reset and counter behavior
  assert property (@(posedge clk_in) rst_in |-> (q_pwm_cnt==6'h00));
  assert property (q_pwm_cnt == $past(q_pwm_cnt) + 6'd1);
  assert property (d_pwm_cnt == (q_pwm_cnt + 6'd1));
  cover  property (q_pwm_cnt==6'd63 ##1 q_pwm_cnt==6'd0);

  // Mute gating
  assert property (pulse0   == (mute_in[0] ? 4'h0 : pulse0_in));
  assert property (pulse1   == (mute_in[1] ? 4'h0 : pulse1_in));
  assert property (triangle == (mute_in[2] ? 4'h0 : triangle_in));
  assert property (noise    == (mute_in[3] ? 4'h0 : noise_in));
  cover  property ($changed(mute_in[0]));
  cover  property ($changed(mute_in[1]));
  cover  property ($changed(mute_in[2]));
  cover  property ($changed(mute_in[3]));

  // Pre-LUT sums and ranges
  assert property (pulse_in_total == (pulse0 + pulse1));
  assert property (pulse_in_total <= 5'h1E);
  assert property (tnd_in_total == ({triangle,1'b0} + {1'b0,triangle} + {noise,1'b0}));
  assert property (tnd_in_total <= 7'h4B);

  // LUT correctness
  assert property (pulse_out === P_LUT[pulse_in_total]);
  assert property (tnd_out   === T_LUT[tnd_in_total]);

  // Mix and PWM compare
  assert property (mixed_out == (pulse_out + tnd_out));      // 6-bit sum truncation by type
  assert property (audio_out == (mixed_out > q_pwm_cnt));    // exact comparator behavior

  // Sanity (no X on key outputs in valid domain)
  assert property (!$isunknown({pulse_out,tnd_out,mixed_out,audio_out}));

  // Functional coverage (key corners)
  cover property (pulse_in_total==5'd0);
  cover property (pulse_in_total==5'd30);
  cover property (tnd_in_total==7'd0);
  cover property (tnd_in_total==7'd75);
  cover property (mixed_out==6'd0);
  cover property (mixed_out==6'd45);
  cover property ($rose(audio_out) or $fell(audio_out));

endmodule