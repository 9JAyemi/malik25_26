// SVA for tone_generator
// Bind this file to the DUT

module tone_generator_sva #(parameter int N = 8) (
  input  logic                  clk,
  input  logic                  reset,
  input  logic [1:0]            mode,
  input  logic [7:0]            freq,
  input  logic signed [N-1:0]   tone,
  input  logic [31:0]           phase_acc,
  input  logic [31:0]           phase_inc
);

  default clocking cb @(posedge clk); endclocking

  localparam int AMP = N-1;

  function automatic logic [31:0] dtmf_inc(input logic [7:0] f);
    case (f)
      8'h11: dtmf_inc = 32'd3486784;
      8'h12: dtmf_inc = 32'd3853932;
      8'h13: dtmf_inc = 32'd4261416;
      8'h14: dtmf_inc = 32'd4706164;
      8'h21: dtmf_inc = 32'd6048840;
      8'h22: dtmf_inc = 32'd6684096;
      8'h23: dtmf_inc = 32'd7389128;
      8'h24: dtmf_inc = 32'd8165376;
      default: dtmf_inc = '0; // unused in mapping assertion guard
    endcase
  endfunction

  // Basic sanity
  ap_reset_hold: assert property (reset |-> (phase_acc==32'd0 && tone==$signed(0)));
  ap_no_x_after_reset: assert property (!reset |-> !($isunknown({mode,freq,tone,phase_acc,phase_inc})));

  // Phase accumulator update (uses previous phase_inc)
  ap_acc_update: assert property ((!reset && !$past(reset))
                                  |-> phase_acc == $past(phase_acc) + $past(phase_inc));

  // Phase increment per mode
  ap_sine_inc:   assert property (disable iff (reset) (mode==2'b01)
                                  |=> phase_inc == (32'd1572864 * $past(freq)));
  ap_square_inc: assert property (disable iff (reset) (mode==2'b10)
                                  |=> phase_inc == (32'd1572864 * $past(freq)));

  // DTMF mapping and default hold
  ap_dtmf_map:   assert property (disable iff (reset)
                                  (mode==2'b00 && (freq inside {8'h11,8'h12,8'h13,8'h14,8'h21,8'h22,8'h23,8'h24}))
                                  |=> phase_inc == dtmf_inc($past(freq)));
  ap_dtmf_hold:  assert property (disable iff (reset)
                                  (mode==2'b00 && !(freq inside {8'h11,8'h12,8'h13,8'h14,8'h21,8'h22,8'h23,8'h24}))
                                  |=> phase_inc == $past(phase_inc)));

  // Tone behavior per mode
  ap_sine_dtmf_msb_tracks_phase: assert property (disable iff (reset)
                                  (mode inside {2'b00,2'b01})
                                  |=> tone[N-1] == $past(phase_acc[31]));

  ap_square_levels_and_polarity: assert property (disable iff (reset)
                                  (mode==2'b10)
                                  |=> (tone == ($past(phase_acc[31]) ? AMP : -AMP)));

  // Unspecified mode (2'b11) holds registers
  ap_mode11_hold: assert property (disable iff (reset)
                                  (mode==2'b11)
                                  |=> (tone == $past(tone) && phase_inc == $past(phase_inc)));

  // Functional coverage
  cv_reset_deassert:  cover property (reset ##1 !reset);
  cv_mode_dtmf:       cover property (!reset && mode==2'b00);
  cv_mode_sine:       cover property (!reset && mode==2'b01);
  cv_mode_square:     cover property (!reset && mode==2'b10);
  cv_mode_undef:      cover property (!reset && mode==2'b11);

  cv_dtmf_11: cover property (!reset && mode==2'b00 && freq==8'h11);
  cv_dtmf_12: cover property (!reset && mode==2'b00 && freq==8'h12);
  cv_dtmf_13: cover property (!reset && mode==2'b00 && freq==8'h13);
  cv_dtmf_14: cover property (!reset && mode==2'b00 && freq==8'h14);
  cv_dtmf_21: cover property (!reset && mode==2'b00 && freq==8'h21);
  cv_dtmf_22: cover property (!reset && mode==2'b00 && freq==8'h22);
  cv_dtmf_23: cover property (!reset && mode==2'b00 && freq==8'h23);
  cv_dtmf_24: cover property (!reset && mode==2'b00 && freq==8'h24);

  cv_square_pos: cover property (disable iff (reset) (mode==2'b10) &&  $rose(phase_acc[31]));
  cv_square_neg: cover property (disable iff (reset) (mode==2'b10) &&  $fell(phase_acc[31]));
  cv_acc_wrap:   cover property (disable iff (reset) (!$past(reset) && (phase_acc < $past(phase_acc))));

endmodule

// Bind into DUT (assumes parameter N from DUT)
bind tone_generator tone_generator_sva #(.N(N)) tone_generator_sva_i (
  .clk       (clk),
  .reset     (reset),
  .mode      (mode),
  .freq      (freq),
  .tone      (tone),
  .phase_acc (phase_acc),
  .phase_inc (phase_inc)
);