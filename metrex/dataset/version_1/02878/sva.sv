// SystemVerilog Assertions for mig_7series_v1_9_ddr_prbs_gen
// Drop inside the module (near the end). Focused, high-quality checks.

`ifndef SYNTHESIS
// Elaboration-time param guard
initial assert (PRBS_WIDTH >= 32)
  else $error("PRBS_WIDTH(%0d) must be >= 32 for taps that use bit 32", PRBS_WIDTH);

// Make $past safe from time 0
logic sva_init;
initial sva_init = 1'b0;
always @(posedge clk_i) sva_init <= 1'b1;

default clocking cb @(posedge clk_i); endclocking

// Short-hands
wire load_cond  = (reseed_prbs_r && clk_en_i) || rst_i || !clk_en_i;
wire shift_en   =  clk_en_i && (~phy_if_empty_r || ~prbs_rdlvl_start);

// 1) Input sync check
assert property (disable iff (!sva_init) (phy_if_empty_r == $past(phy_if_empty)))
  else $error("phy_if_empty_r must equal previous phy_if_empty");

// 2) Counter/reset/gating behavior
assert property ( (rst_i || !clk_en_i) |-> (sample_cnt_r == '0 && reseed_prbs_r == 1'b0) )
  else $error("Counter/reseed not cleared on rst or !clk_en");

assert property ( shift_en |-> sample_cnt_r == $past(sample_cnt_r) + 1 )
  else $error("sample_cnt_r must increment when enabled");

assert property ( clk_en_i && (phy_if_empty_r && prbs_rdlvl_start) && !rst_i
                  |-> sample_cnt_r == $past(sample_cnt_r) )
  else $error("sample_cnt_r must hold when not shifting");

// 3) Reseed pulse generation (only when actively counting)
assert property ( shift_en |-> (reseed_prbs_r == (sample_cnt_r == PRBS_SEQ_LEN_CYCLES-2)) )
  else $error("reseed_prbs_r must assert only at sample_cnt_r==PRBS_SEQ_LEN_CYCLES-2");

assert property ( clk_en_i && (phy_if_empty_r && prbs_rdlvl_start) && !rst_i
                  |-> reseed_prbs_r == $past(reseed_prbs_r) )
  else $error("reseed_prbs_r must hold value when not updating");

// 4) LFSR load/check on reseed/reset/!clk_en
assert property ( load_cond
                  |-> (lfsr_q[4:1] == (prbs_seed_i[3:0] | 4'h5) &&
                       lfsr_q[PRBS_WIDTH:5] == prbs_seed_i[PRBS_WIDTH-1:4]) )
  else $error("LFSR load from seed mismatch");

// Non-all-zero protection on any load/shift event
assert property ( (load_cond || shift_en) |-> (lfsr_q != '0) )
  else $error("LFSR reached all-zero state");

// 5) LFSR shift behavior (when not loading)
assert property ( shift_en && !load_cond
                  |-> lfsr_q[PRBS_WIDTH:31] == $past(lfsr_q[PRBS_WIDTH-1:30]) )
  else $error("LFSR upper slice shift mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[30] == ($past(lfsr_q[16]) ^ $past(lfsr_q[13]) ^ $past(lfsr_q[5]) ^ $past(lfsr_q[1])) )
  else $error("LFSR bit[30] tap mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[29:9] == $past(lfsr_q[28:8]) )
  else $error("LFSR mid slice shift mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[8] == ($past(lfsr_q[32]) ^ $past(lfsr_q[7])) )
  else $error("LFSR bit[8] tap mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[7] == ($past(lfsr_q[32]) ^ $past(lfsr_q[6])) )
  else $error("LFSR bit[7] tap mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[6:4] == $past(lfsr_q[5:3]) )
  else $error("LFSR bits[6:4] shift mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[3] == ($past(lfsr_q[32]) ^ $past(lfsr_q[2])) )
  else $error("LFSR bit[3] tap mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[2] == $past(lfsr_q[1]) )
  else $error("LFSR bit[2] shift mismatch");

assert property ( shift_en && !load_cond
                  |-> lfsr_q[1] == $past(lfsr_q[32]) )
  else $error("LFSR bit[1] tap mismatch");

// 6) Hold when neither load nor shift
assert property ( !load_cond && !shift_en |-> lfsr_q == $past(lfsr_q) )
  else $error("LFSR must hold when idle");

// 7) Output mapping
assert property ( prbs_o == lfsr_q[PRBS_WIDTH:1] )
  else $error("prbs_o must mirror lfsr_q[PRBS_WIDTH:1]");

// 8) Useful functional coverage
cover property ( shift_en );
cover property ( shift_en && (sample_cnt_r == PRBS_SEQ_LEN_CYCLES-2) ##1 (reseed_prbs_r && clk_en_i) );
cover property ( !clk_en_i ##1 load_cond ); // load due to !clk_en_i
cover property ( (phy_if_empty_r && prbs_rdlvl_start && clk_en_i) [*3] ); // idle hold window
cover property ( shift_en && (sample_cnt_r == {PRBS_SEQ_LEN_CYCLES_BITS{1'b1}}) ##1 (sample_cnt_r == '0) ); // wrap
`endif