// SystemVerilog Assertions for LogicProbe system
// Bind these to the DUT modules. Focused, high-signal-quality checks and key coverage.

//////////////////////////////////////////////////////////
// Top-level: LogicProbe
//////////////////////////////////////////////////////////
module LogicProbe_sva(
  input  logic        clock,
  input  logic        reset,
  input  logic        trigger,
  input  logic        sample,
  input  logic [127:0]channels,
  output logic        serial_out,

  input  logic        full,
  input  logic [12:0] rdaddr,
  input  logic [7:0]  data,
  input  logic        write,
  input  logic        ready,
  input  logic        done,
  input  logic        state
);
  default clocking cb @(posedge clock); endclocking

  // Reset values
  a_lp_reset_vals: assert property (reset |-> (rdaddr==13'd0 && write==0 && done==0 && state==0));

  // No activity unless reading window is open
  a_lp_no_write_when_not_active: assert property (disable iff (reset) (!full || done) |-> (!write && $stable({rdaddr,state,done})));

  // Write is 1-cycle pulse; state mirrors write
  a_lp_write_pulse:  assert property (disable iff (reset) write |=> !write);
  a_lp_state_eq_write: assert property (disable iff (reset) state == write);

  // Write only when previously allowed (ready, active, state==0)
  a_lp_write_only_when_ready: assert property (disable iff (reset) write |-> $past(full && !done && ready && (state==0)));

  // Address management on write
  a_lp_addr_increments_on_write: assert property (disable iff (reset) write |=> rdaddr == $past(rdaddr)+13'd1);
  a_lp_addr_change_only_from_state1: assert property (disable iff (reset) (rdaddr != $past(rdaddr)) |-> $past(full && !done && state==1));

  // Terminal condition and stickiness
  a_lp_done_on_last_addr: assert property (disable iff (reset) $past(write && ($past(rdaddr)==13'd8191)) |-> (done && rdaddr==13'd0));
  a_lp_done_sticky:       assert property (disable iff (reset) done |=> done);
  a_lp_no_writes_after_done: assert property (disable iff (reset) done |-> !write);

  // Key coverage: reach full transfer and finish
  c_lp_start_to_done: cover property (disable iff (reset) full ##[1:$] done);
  c_lp_hit_last_addr: cover property (disable iff (reset) rdaddr==13'd8191);
  c_lp_any_write:     cover property (disable iff (reset) write);

endmodule

bind LogicProbe LogicProbe_sva LP_SVA (.*);

//////////////////////////////////////////////////////////
// Sampler: LogicProbe_sampler
//////////////////////////////////////////////////////////
module LogicProbe_sampler_sva(
  input  logic        clock,
  input  logic        reset,
  input  logic        trigger,
  input  logic        sample,
  input  logic [127:0]data_in,
  input  logic [12:0] rdaddr,

  input  logic        full,
  input  logic [8:0]  wraddr,
  input  logic [3:0]  muxctrl,
  input  logic        triggered,
  input  logic [7:0]  data_out
);
  default clocking cb @(posedge clock); endclocking

  // Reset values
  a_sm_reset_vals: assert property (reset |-> (wraddr==9'd0 && triggered==0 && full==0));

  // Trigger/sample behavior and fill
  a_sm_inc_on_sample_after_trig: assert property (disable iff (reset)
    $past(triggered && sample && !full && (wraddr!=9'd511)) |-> (wraddr==$past(wraddr)+9'd1 && !full));

  a_sm_full_on_last_entry: assert property (disable iff (reset)
    $past(triggered && sample && (wraddr==9'd511)) |-> (full && wraddr==$past(wraddr)));

  a_sm_first_sample_on_trigger: assert property (disable iff (reset)
    $past(!triggered && trigger && sample) |-> wraddr==$past(wraddr)+9'd1);

  a_sm_no_inc_if_no_sample_on_trigger: assert property (disable iff (reset)
    $past(!triggered && trigger && !sample) |-> wraddr==$past(wraddr));

  // After full, write address freezes
  a_sm_wraddr_freeze_when_full: assert property (disable iff (reset) full |-> $stable(wraddr));
  a_sm_full_sticky:             assert property (disable iff (reset) full |=> full);

  // Mux control tracks rdaddr low nibble, 1-cycle registered
  a_sm_mux_tracks_rdaddr: assert property (disable iff (reset) muxctrl == $past(rdaddr[3:0]));

  // Coverage: see all muxctrl values during readout phase
  genvar i;
  generate
    for (i=0;i<16;i++) begin: C_SM_MUX
      cover property (disable iff (reset) full && (muxctrl == i[3:0]));
    end
  endgenerate

  // Coverage: capture to full
  c_sm_trigger_to_full: cover property (disable iff (reset) (!triggered && trigger) ##[0:$] full);

endmodule

bind LogicProbe_sampler LogicProbe_sampler_sva SM_SVA (.*);

//////////////////////////////////////////////////////////
// Transmit buffer: LogicProbe_xmtbuf
//////////////////////////////////////////////////////////
module LogicProbe_xmtbuf_sva(
  input  logic       clock,
  input  logic       reset,
  input  logic       write,
  input  logic [7:0] data_in,
  input  logic       serial_out,

  input  logic [1:0] state,
  input  logic [7:0] data_hold,
  input  logic       load,
  input  logic       ready,
  input  logic       empty
);
  default clocking cb @(posedge clock); endclocking

  // Reset values
  a_xb_reset_vals: assert property (reset |-> (state==2'b00 && ready && !load));

  // IDLE accept write -> load immediately
  a_xb_idle_load: assert property (disable iff (reset) (state==2'b00 && write) |-> (load && !ready));

  // One-cycle staging state
  a_xb_01_next: assert property (disable iff (reset) (state==2'b01) |=> (state==2'b10 && ready && !load));

  // State 10 transitions
  a_xb_10_to_00: assert property (disable iff (reset) (state==2'b10 && empty && !write) |=> (state==2'b00 && ready && !load));
  a_xb_10_to_01: assert property (disable iff (reset) (state==2'b10 && empty &&  write) |=> (state==2'b01 && !ready && load));
  a_xb_10_to_11: assert property (disable iff (reset) (state==2'b10 && !empty && write) |=> (state==2'b11 && !ready && !load));

  // State 11 transition when tx empties
  a_xb_11_to_01: assert property (disable iff (reset) (state==2'b11 && empty) |=> (state==2'b01 && !ready && load));
  a_xb_11_hold_when_busy: assert property (disable iff (reset) (state==2'b11 && !empty) |=> state==2'b11);

  // Load only asserted in state 01
  a_xb_load_only_in_01: assert property (disable iff (reset) load |-> state==2'b01);

  // Coverage of key paths
  c_xb_idle_path:  cover property (disable iff (reset) state==2'b00 && write);
  c_xb_busy_path:  cover property (disable iff (reset) state==2'b10 && !empty && write);
  c_xb_queue_path: cover property (disable iff (reset) state==2'b11 && empty);

endmodule

bind LogicProbe_xmtbuf LogicProbe_xmtbuf_sva XB_SVA (.*);

//////////////////////////////////////////////////////////
// UART-like transmitter: LogicProbe_xmt
//////////////////////////////////////////////////////////
module LogicProbe_xmt_sva(
  input  logic       clock,
  input  logic       reset,
  input  logic       load,
  input  logic       empty,
  input  logic [7:0] parallel_in,
  input  logic       serial_out,

  input  logic [3:0] state,
  input  logic [8:0] shift,
  input  logic [10:0]count
);
  default clocking cb @(posedge clock); endclocking

  // Reset values
  a_tx_reset_vals: assert property (reset |-> (state==4'h0 && shift==9'b111_111_111 && empty));

  // Load behavior from idle
  a_tx_load_from_idle: assert property (disable iff (reset)
    $past(state==4'h0 && load) |-> (state==4'h1 && !empty && count==11'd1302 && serial_out==1'b0));

  // Empty implies idle and idle-line high
  a_tx_empty_idle: assert property (disable iff (reset) empty |-> (state==4'h0 && serial_out==1'b1));

  // Active counting and shifting
  a_tx_count_down: assert property (disable iff (reset)
    (state inside {[4'h1:4'hA]}) && (count>0) |=> (state==$past(state) && count==$past(count)-11'd1));

  a_tx_shift_on_zero: assert property (disable iff (reset)
    (state inside {[4'h1:4'hA]}) && (count==0) |=> (state==$past(state)+4'h1 && count==11'd1302 && shift==={1'b1,$past(shift[8:1])}));

  // End of frame -> idle, empty high
  a_tx_b_to_idle: assert property (disable iff (reset) (state==4'hb) |=> (state==4'h0 && empty));

  // Coverage: complete frame
  c_tx_frame: cover property (disable iff (reset) load ##[1:$] (state==4'hb) ##1 empty);

endmodule

bind LogicProbe_xmt LogicProbe_xmt_sva TX_SVA (.*);