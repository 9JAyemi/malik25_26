// SVA for rotator and top_module
// Bind into DUTs; focuses on functional correctness, counters, and interface

bind rotator rotator_sva();
module rotator_sva;
  localparam int W = $bits(shift_reg);
  default clocking cb @(posedge clk); endclocking

  // Sanity
  a_no_x_ctrl: assert property (!$initstate |-> !$isunknown({load,ena}));

  // Output mirrors internal register (one-cycle latency)
  a_q_tracks_shift_reg: assert property (!$initstate |-> q == $past(shift_reg));

  // Load has priority and resets counter
  a_load_behavior: assert property (load |-> (shift_reg == data && shift_cnt == 7'd0));

  // Right rotate by 1 when ena==00 and not loading; counter increments
  a_right_rotate: assert property (
    !$initstate && !load && (ena == 2'b00)
    |-> (shift_reg == { $past(shift_reg)[0], $past(shift_reg)[W-1:1] })
        && (shift_cnt == $past(shift_cnt)+7'd1)
  );

  // Left rotate by 1 when ena==01 and not loading; counter increments
  a_left_rotate: assert property (
    !$initstate && !load && (ena == 2'b01)
    |-> (shift_reg == { $past(shift_reg)[W-2:0], $past(shift_reg)[W-1] })
        && (shift_cnt == $past(shift_cnt)+7'd1)
  );

  // No-rotation case (ena==10 or 11) holds data and clears counter
  a_no_rotate_case: assert property (
    !load && !(ena inside {2'b00,2'b01})
    |-> $stable(shift_reg) && (shift_cnt == 7'd0)
  );

  // Counter only changes on rotate cycles
  a_cnt_changes_only_on_rotate: assert property (
    !$initstate && (shift_cnt != $past(shift_cnt))
    |-> (!load && (ena inside {2'b00,2'b01}))
  );

  // Coverage
  c_load:               cover property (load);
  c_right_seen:         cover property (!load && ena==2'b00);
  c_left_seen:          cover property (!load && ena==2'b01);
  c_no_rotate_seen:     cover property (!load && !(ena inside {2'b00,2'b01}));
  c_cnt_wrap:           cover property (!$initstate && !load && (ena inside {2'b00,2'b01}) && ($past(shift_cnt)==7'h7F) && (shift_cnt==7'h00));
  c_boundary_right:     cover property (!$initstate && !load && ena==2'b00 && (shift_reg[W-1] == $past(shift_reg)[0]));
  c_boundary_left:      cover property (!$initstate && !load && ena==2'b01 && (shift_reg[0]   == $past(shift_reg)[W-1]));
endmodule


bind top_module top_module_sva();
module top_module_sva;
  // Top-level passthrough matches rotator output
  a_top_passthrough: assert property (@(posedge clk) q == rotator_inst.q);
endmodule