// Assertions for ddr3_eim_cs1
// Place inside the module or bind to it. Uses synchronous, active-high reset.
`ifndef DDR3_EIM_CS1_SVA
`define DDR3_EIM_CS1_SVA

// synopsys translate_off
// pragma translate_off
`ifdef ASSERT_ON
default clocking cb @(posedge clk); endclocking
default disable iff (reset)

// Basic command encoding/mapping
assert property (ddr3_rd_cmd == 3'b001);
assert property (ddr3_rd_adr[1:0] == 2'b00);
assert property (ddr3_rd_cmd_en == cmd_go);
assert property (ddr3_rd_bl == {num_pkts,1'b0} - 6'b1);

// Command capture and immediate issue mapping (1-cycle later)
property p_cmd_capture_issue;
  ctl_stb |=> (cmd_adr == $past(ctl[29:0]) &&
               num_pkts == $past(ctl[36:32]) &&
               ddr3_rd_cmd_en == ($past(ctl[36:32]) != 5'b0) &&
               ddr3_rd_adr == {$past(ctl[29:2]),2'b00} &&
               ddr3_rd_bl == {$past(ctl[36:32]),1'b0} - 6'b1);
endproperty
assert property (p_cmd_capture_issue);

// cmd_go definition consistent with ctl_stb/num_pkts
assert property (cmd_go == (ctl_stb && (ctl[36:32] != 5'b0)));
assert property ($rose(cmd_go) |-> $past(ctl_stb && (ctl[36:32] != 5'b0)));

// Registers stability without new control
assert property (!ctl_stb |=> (cmd_adr == $past(cmd_adr) && num_pkts == $past(num_pkts)));

// Status bus mapping
assert property (status == {readcount,
                            3'b000, cmd_err,
                            ddr3_rd_cmd_empty, ddr3_rd_cmd_full, ddr3_rd_empty, ddr3_rd_full,
                            1'b0, ddr3_rd_count[6:0]});

// Readcount behavior: reset on ctl_stb, inc on rd_stb, hold otherwise
assert property (ctl_stb |=> (readcount == 8'h00));
assert property (!ctl_stb && rd_stb |=> (readcount == $past(readcount) + 8'd1));
assert property (!ctl_stb && !rd_stb |=> (readcount == $past(readcount)));

// State machine one-hot and next-state behavior
localparam READ_IDLE        = 6'b000001;
localparam READ_PENDING     = 6'b000010;
localparam READ_FETCH       = 6'b000100;
localparam READ_UPDATE_LSB  = 6'b001000;
localparam READ_UPDATE_MSB  = 6'b010000;
localparam READ_WAIT        = 6'b100000;

assert property ($onehot0(cstate));
assert property ($onehot0(nstate));

// Transitions
assert property ((cstate == READ_IDLE) &&  cmd_go |=> (cstate == READ_PENDING));
assert property ((cstate == READ_IDLE) && !cmd_go |=> (cstate == READ_IDLE));

assert property ((cstate == READ_PENDING) && (outstanding != 0) && (ddr3_rd_count < 7'd2) |=> (cstate == READ_PENDING));
assert property ((cstate == READ_PENDING) && (outstanding != 0) && (ddr3_rd_count >= 7'd2) |=> (cstate == READ_FETCH));
assert property ((cstate == READ_PENDING) && (outstanding == 0) |=> (cstate == READ_IDLE));

assert property ((cstate == READ_FETCH)       |=> (cstate == READ_UPDATE_LSB));
assert property ((cstate == READ_UPDATE_LSB)  |=> (cstate == READ_UPDATE_MSB));
assert property ((cstate == READ_UPDATE_MSB)  |=> (cstate == READ_WAIT));

assert property ((cstate == READ_WAIT) &&  rd_stb |=> (cstate == READ_PENDING));
assert property ((cstate == READ_WAIT) && !rd_stb |=> (cstate == READ_WAIT));

// Outstanding update rules and no underflow
assert property ((cstate == READ_IDLE)       |=> (outstanding == $past(num_pkts)));
assert property ((cstate == READ_UPDATE_MSB) |=> (outstanding == $past(outstanding) - 5'd1));
assert property ((cstate == READ_UPDATE_MSB) |->  ($past(outstanding) != 5'd0));
assert property ((cstate inside {READ_PENDING,READ_FETCH,READ_UPDATE_LSB,READ_WAIT}) |=> (outstanding == $past(outstanding)));

// Read enable behavior and safety
assert property ((cstate == READ_IDLE) -> (ddr3_rd_en == (ddr3_rd_count > 7'd0)));
assert property ((cstate == READ_FETCH)      -> ddr3_rd_en);
assert property ((cstate == READ_UPDATE_LSB) -> ddr3_rd_en);
assert property ((cstate inside {READ_PENDING,READ_UPDATE_MSB,READ_WAIT}) -> !ddr3_rd_en);
assert property (ddr3_rd_en |-> (ddr3_rd_count > 7'd0)); // never read when empty

// rd_cache assembly check: two 32b beats -> 64b word {MSB,LSB}
property p_cache_assembled;
  (cstate == READ_UPDATE_MSB) |=> (rd_cache == {$past(ddr3_rd_data), $past(ddr3_rd_data,2)});
endproperty
assert property (p_cache_assembled);

// Error handling for command FIFO full
assert property (reset_errors == $past(ctl[63]));      // reset_errors is 1-cycle delayed ctl[63]
assert property (reset_errors |-> (cmd_err == 1'b0));  // clear takes priority same cycle
assert property ((cmd_go && ddr3_rd_cmd_full && !reset_errors) |=> cmd_err);
assert property ((!reset_errors && !(cmd_go && ddr3_rd_cmd_full)) |=> (cmd_err == $past(cmd_err)));

// Covers
cover property (ctl_stb && (ctl[36:32] != 0) ##1
                (cstate == READ_PENDING) ##1
                (cstate == READ_FETCH) ##1
                (cstate == READ_UPDATE_LSB) ##1
                (cstate == READ_UPDATE_MSB) ##1
                (cstate == READ_WAIT) ##1
                rd_stb ##1
                (cstate == READ_PENDING));

cover property (cmd_go && ddr3_rd_cmd_full ##1 cmd_err);
cover property ((cstate == READ_PENDING) && (outstanding == 0) ##1 (cstate == READ_IDLE));
`endif
// pragma translate_on
// synopsys translate_on
`endif // DDR3_EIM_CS1_SVA