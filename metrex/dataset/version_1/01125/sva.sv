// SVA for barrel_shifter_4bit
// Bind into DUT: bind barrel_shifter_4bit barrel_shifter_4bit_sva i_sva(.*);

module barrel_shifter_4bit_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic        load,
  input logic        reset,
  input logic [1:0]  shift,
  input logic        shift_dir,
  input logic [3:0]  Q
);

  // Track availability of $past()
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Golden next-state model for shift/rotate
  function automatic logic [3:0] next_q_model (logic [3:0] q_prev,
                                               logic [1:0] s,
                                               logic       dir);
    logic [3:0] n;
    unique case (s)
      2'b00: n = q_prev;
      2'b01: n = dir ? {1'b0,  q_prev[3:1]} : {q_prev[2:0], 1'b0};
      2'b10: n = dir ? {2'b00, q_prev[3:2]} : {q_prev[1:0], 2'b00};
      2'b11: n = dir ? {q_prev[0], q_prev[3:1]} : {q_prev[2:0], q_prev[3]};
    endcase
    return n;
  endfunction

  // Next-state functional correctness with proper priority: reset > load > shift/rotate
  ap_next_state: assert property (@(posedge clk) disable iff (!past_valid)
    ($past(reset))                             ? (Q == 4'b0000) :
    ($past(load)  && !$past(reset))            ? (Q == $past(A)) :
                                                 (Q == next_q_model($past(Q), $past(shift), $past(shift_dir)))
  );

  // Controls should be known (no X/Z) at sampling
  ap_ctrl_known: assert property (@(posedge clk) !$isunknown({reset, load, shift_dir, shift}));

  // Q changes only on posedge clk (glitch-free between clocks)
  ap_sync_only:  assert property (@(negedge clk) $stable(Q));

  // Coverage: exercise all behaviors
  cv_reset:      cover property (@(posedge clk) $past(reset));
  cv_load:       cover property (@(posedge clk) !$past(reset) && $past(load));
  cv_hold:       cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b00));
  cv_sh1_l:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b01) && !$past(shift_dir));
  cv_sh1_r:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b01) &&  $past(shift_dir));
  cv_sh2_l:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b10) && !$past(shift_dir));
  cv_sh2_r:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b10) &&  $past(shift_dir));
  cv_rot_l:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b11) && !$past(shift_dir));
  cv_rot_r:      cover property (@(posedge clk) !$past(reset) && !$past(load) && ($past(shift)==2'b11) &&  $past(shift_dir));

endmodule

// Bind example:
// bind barrel_shifter_4bit barrel_shifter_4bit_sva i_sva(.*);