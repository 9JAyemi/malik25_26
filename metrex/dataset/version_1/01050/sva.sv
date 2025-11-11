// SVA for omsp_clock_mux
// Bind into the DUT to check key invariants, handshakes, and coverage
module omsp_clock_mux_sva (
  input        clk_in0,
  input        clk_in1,
  input        clk_in0_scan_fix_inv,
  input        clk_in1_scan_fix_inv,
  input        reset,
  input        scan_mode,
  input        select_in,

  input        clk_out,

  input        clk_in0_inv,
  input        clk_in1_inv,

  input        gated_clk_in0,
  input        gated_clk_in1,

  input        in0_select,
  input        in0_select_s,
  input        in0_select_ss,
  input        in0_enable,

  input        in1_select,
  input        in1_select_s,
  input        in1_select_ss,
  input        in1_enable
);

  // Basic combinational relations (checked on any clock edge)
  // Inverters and gating equivalence
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   clk_in0_inv == ~clk_in0);
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   clk_in1_inv == ~clk_in1);

  // Select equations
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   in0_select == (~select_in & ~in1_select_ss));
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   in1_select == ( select_in & ~in0_select_ss));

  // Enables
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   in0_enable == (in0_select_ss |  scan_mode));
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   in1_enable == (in1_select_ss & ~scan_mode));

  // Gated clock behavior
  assert property (@(posedge clk_in0 or negedge clk_in0) (in0_enable == 1'b0) |-> (gated_clk_in0 == 1'b1));
  assert property (@(posedge clk_in1 or negedge clk_in1) (in1_enable == 1'b0) |-> (gated_clk_in1 == 1'b1));
  assert property (@(posedge clk_in0 or negedge clk_in0) (in0_enable == 1'b1) |-> (gated_clk_in0 == clk_in0));
  assert property (@(posedge clk_in1 or negedge clk_in1) (in1_enable == 1'b1) |-> (gated_clk_in1 == clk_in1));

  // Output must equal selected source (or 1 when none)
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   (in0_enable && !in1_enable) |-> (clk_out == clk_in0));
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   (in1_enable && !in0_enable) |-> (clk_out == clk_in1));
  assert property (@(posedge clk_in0 or negedge clk_in0 or posedge clk_in1 or negedge clk_in1)
                   (!in0_enable && !in1_enable) |-> (clk_out == 1'b1));

  // Mutual exclusion (critical for glitch-free muxing)
  assert property (@(posedge clk_in0 or posedge clk_in1) !(in0_enable && in1_enable));
  assert property (@(posedge clk_in0 or posedge clk_in1) !(in0_select_ss && in1_select_ss));
  assert property (@(posedge clk_in0 or posedge clk_in1) !(in0_select && in1_select));

  // Reset behavior (async reset forces default select 0)
  assert property (@(posedge clk_in0 or posedge clk_in1 or posedge clk_in0_scan_fix_inv or posedge clk_in1_scan_fix_inv)
                   reset |-> (in0_select_s && in0_select_ss && !in1_select_s && !in1_select_ss
                              && in0_enable && !in1_enable));

  // Two-stage synchronizers: capture correctness
  assert property (@(posedge clk_in0_scan_fix_inv) disable iff (reset)
                   in0_select_s == $past(in0_select));
  assert property (@(posedge clk_in0) disable iff (reset)
                   in0_select_ss == $past(in0_select_s));

  assert property (@(posedge clk_in1_scan_fix_inv) disable iff (reset)
                   in1_select_s == $past(in1_select));
  assert property (@(posedge clk_in1) disable iff (reset)
                   in1_select_ss == $past(in1_select_s));

  // No overlap on enable transitions
  assert property (@(posedge clk_in0 or posedge clk_in1) $rose(in0_enable) |-> !in1_enable);
  assert property (@(posedge clk_in0 or posedge clk_in1) $rose(in1_enable) |-> !in0_enable);

  // Scan mode forces clk0 path only
  assert property (@(posedge clk_in0 or posedge clk_in1)
                   scan_mode |-> (in0_enable && !in1_enable && (clk_out == clk_in0)));

  // Coverage: exercise both selections and scan behavior
  cover property (@(posedge clk_in0 or posedge clk_in1)
                  !scan_mode && !select_in && in0_enable && !in1_enable
                  ##[1:$] $rose(select_in)
                  ##[1:$] (in1_enable && !in0_enable) ##[1:$] $fell(select_in)
                  ##[1:$] (in0_enable && !in1_enable));

  cover property (@(posedge clk_in0 or posedge clk_in1)
                  !scan_mode && in1_enable && !in0_enable
                  ##1 $rose(scan_mode)
                  ##1 (in0_enable && !in1_enable) ##[1:$] $fell(scan_mode));

endmodule

bind omsp_clock_mux omsp_clock_mux_sva u_omsp_clock_mux_sva (.*);