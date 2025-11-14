// SystemVerilog Assertions for axis_gate_controller
// Place inside the module or bind to it. Focused, high-value checks and coverage.

`ifndef SYNTHESIS
// default clocking and reset
default clocking cb @(posedge aclk); endclocking
default disable iff (!aresetn)

// Basic X-checks on visible outputs
assert property (!$isunknown({s_axis_tready, dout, poff, level})))
  else $error("X on outputs");

// Reset values
assert property (!aresetn |=> (int_tready_reg==0 && int_dout_reg==0 && int_enbl_reg==0 &&
                               int_cntr_reg==0 && int_data_reg==0));

// Output mappings always match internal regs
assert property (s_axis_tready == int_tready_reg);
assert property (dout == int_dout_reg);
assert property (poff == int_data_reg[95:64]);
assert property (level == int_data_reg[111:96]);

// Handshake/start capture behavior
sequence start_evt; (!int_enbl_reg && s_axis_tvalid); endsequence

// Start event causes 1-cycle TREADY pulse, enable, counter clear, and data capture
assert property (start_evt |=> (int_tready_reg && int_enbl_reg && int_cntr_reg==0 &&
                                int_data_reg == $past(s_axis_tdata)));

// TREADY is a single-cycle pulse and only in response to a valid start
assert property (int_tready_reg |-> $past(!int_enbl_reg && s_axis_tvalid));
assert property (int_tready_reg |=> !int_tready_reg);
assert property (!int_tready_reg or !$past(int_tready_reg)); // no back-to-back highs

// While enabled, data/fields are stable; counter increments by 1
assert property (int_enbl_reg |=> (int_cntr_reg == $past(int_cntr_reg)+1));
assert property (int_enbl_reg |-> ($stable(int_data_reg) && $stable(poff) && $stable(level)));

// When idle and not starting, counter holds and dout is 0
assert property ((!int_enbl_reg && !(s_axis_tvalid)) |=> (int_cntr_reg==$past(int_cntr_reg) && !int_dout_reg));

// dout behavior:
// First active cycle (cntr==0) with nonzero end -> next cycle dout = |level
assert property ((int_enbl_reg && int_cntr_reg==64'd0 && (int_data_reg[63:0] != 64'd0))
                 |=> (int_dout_reg == (|int_data_reg[111:96])));

// Zero-length end: immediately deassert enable and keep dout low
assert property ((int_enbl_reg && int_cntr_reg==64'd0 && (int_data_reg[63:0] == 64'd0))
                 |=> (!int_enbl_reg && !int_dout_reg));

// During middle of window, dout holds its value
assert property ((int_enbl_reg && (int_cntr_reg > 64'd0) && (int_cntr_reg != int_data_reg[63:0]))
                 |=> $stable(int_dout_reg));

// At end count, next cycle disable and dout low
assert property ((int_enbl_reg && (int_cntr_reg == int_data_reg[63:0]))
                 |=> (!int_enbl_reg && !int_dout_reg));

// When not enabled, dout is 0
assert property (!int_enbl_reg |-> !int_dout_reg);

// Enable persistence until end
assert property ((int_enbl_reg && (int_cntr_reg != int_data_reg[63:0])) |=> int_enbl_reg);

// Coverage: typical scenarios
// 1) Normal capture with nonzero level and end=1: single-cycle dout pulse
cover property (start_evt ##1 (int_enbl_reg && int_cntr_reg==0 && int_data_reg[63:0]==64'd1 && (|int_data_reg[111:96]))
                ##1 (dout) ##1 (!dout));

// 2) Normal capture with nonzero level and end=2: two-cycle dout pulse
cover property (start_evt ##1 (int_enbl_reg && int_cntr_reg==0 && int_data_reg[63:0]==64'd2 && (|int_data_reg[111:96]))
                ##2 (dout[*2]) ##1 (!dout));

// 3) level==0 (dout should never assert while enabled)
cover property (start_evt ##1 (int_enbl_reg && int_cntr_reg==0 && (int_data_reg[63:0] > 0) && (int_data_reg[111:96]==16'd0))
                ##[1:$] (!dout) ##1 (!int_enbl_reg));

// 4) Zero-length end (immediate disable)
cover property (start_evt ##1 (int_enbl_reg && int_cntr_reg==0 && int_data_reg[63:0]==64'd0)
                ##1 (!int_enbl_reg && !dout));

`endif