// SVA for drp_other_registers
// Concise, high-quality checks and coverage. Bind into DUT to see internal regs.

module drp_other_registers_sva #(
  parameter int DRP_ABITS = 8,
  parameter int DRP_REG0  = 8,
  parameter int DRP_REG1  = 9,
  parameter int DRP_REG2  = 10,
  parameter int DRP_REG3  = 11
)(
  // DUT ports
  input  logic                  drp_clk,
  input  logic                  drp_rst,
  input  logic                  drp_en,
  input  logic                  drp_we,
  input  logic [DRP_ABITS-1:0]  drp_addr,
  input  logic [15:0]           drp_di,
  input  logic                  drp_rdy,
  input  logic [15:0]           drp_do,
  input  logic [15:0]           drp_register0,
  input  logic [15:0]           drp_register1,
  input  logic [15:0]           drp_register2,
  input  logic [15:0]           drp_register3,
  // DUT internals (matched by name via bind)
  input  logic [DRP_ABITS-1:0]  drp_addr_r,
  input  logic                  drp_wr_r,
  input  logic [1:0]            drp_rd_r,
  input  logic [15:0]           drp_di_r,
  input  logic                  drp_reg0_set,
  input  logic                  drp_reg1_set,
  input  logic                  drp_reg2_set,
  input  logic                  drp_reg3_set,
  input  logic                  drp_reg0_get,
  input  logic                  drp_reg1_get,
  input  logic                  drp_reg2_get,
  input  logic                  drp_reg3_get,
  input  logic [15:0]           drp_register0_r,
  input  logic [15:0]           drp_register1_r,
  input  logic [15:0]           drp_register2_r,
  input  logic [15:0]           drp_register3_r
);

  // Static parameter sanity
  initial begin
    assert (DRP_REG0 < (1<<DRP_ABITS) && DRP_REG1 < (1<<DRP_ABITS) &&
            DRP_REG2 < (1<<DRP_ABITS) && DRP_REG3 < (1<<DRP_ABITS))
      else $error("DRP_REGx exceeds DRP_ABITS range");
    assert ((DRP_REG0!=DRP_REG1)&&(DRP_REG0!=DRP_REG2)&&(DRP_REG0!=DRP_REG3)&&
            (DRP_REG1!=DRP_REG2)&&(DRP_REG1!=DRP_REG3)&&(DRP_REG2!=DRP_REG3))
      else $error("DRP_REGx parameters must be unique");
  end

  // Past-valid gating to avoid $past issues
  logic past_valid;
  always_ff @(posedge drp_clk or posedge drp_rst) begin
    if (drp_rst) past_valid <= 1'b0;
    else         past_valid <= 1'b1;
  end

  default clocking cb @(posedge drp_clk); endclocking
  // Disable most checks until one active cycle after reset
  default disable iff (!past_valid);

  // Reset effects
  assert property (@(posedge drp_clk) drp_rst |=> (drp_register0_r==16'h0 &&
                                                   drp_register1_r==16'h0 &&
                                                   drp_register2_r==16'h0 &&
                                                   drp_register3_r==16'h0));

  // Output mirrors
  assert property (drp_register0 == drp_register0_r);
  assert property (drp_register1 == drp_register1_r);
  assert property (drp_register2 == drp_register2_r);
  assert property (drp_register3 == drp_register3_r);

  // Pipeline captures
  assert property (drp_addr_r == $past(drp_addr));
  assert property (drp_di_r   == $past(drp_di));
  assert property (drp_wr_r   == $past(drp_we && drp_en));
  assert property (drp_rd_r[0]== $past(~drp_we && drp_en));
  assert property (drp_rd_r[1]== $past(drp_rd_r[0]));

  // Decode: set/get equals previous-stage conditions
  assert property (drp_reg0_set == ($past(drp_wr_r)   && ($past(drp_addr_r)==DRP_REG0)));
  assert property (drp_reg1_set == ($past(drp_wr_r)   && ($past(drp_addr_r)==DRP_REG1)));
  assert property (drp_reg2_set == ($past(drp_wr_r)   && ($past(drp_addr_r)==DRP_REG2)));
  assert property (drp_reg3_set == ($past(drp_wr_r)   && ($past(drp_addr_r)==DRP_REG3)));

  assert property (drp_reg0_get == ($past(drp_rd_r[0])&& ($past(drp_addr_r)==DRP_REG0)));
  assert property (drp_reg1_get == ($past(drp_rd_r[0])&& ($past(drp_addr_r)==DRP_REG1)));
  assert property (drp_reg2_get == ($past(drp_rd_r[0])&& ($past(drp_addr_r)==DRP_REG2)));
  assert property (drp_reg3_get == ($past(drp_rd_r[0])&& ($past(drp_addr_r)==DRP_REG3)));

  // One-hot (or none) on set/get
  assert property ($onehot0({drp_reg0_set,drp_reg1_set,drp_reg2_set,drp_reg3_set}));
  assert property ($onehot0({drp_reg0_get,drp_reg1_get,drp_reg2_get,drp_reg3_get}));

  // Ready timing/definition
  assert property (drp_rdy == ($past(drp_wr_r) || $past(drp_rd_r[1])));
  assert property ((drp_en &&  drp_we) |-> ##2 drp_rdy); // write -> rdy in 2
  assert property ((drp_en && !drp_we) |-> ##3 drp_rdy); // read  -> rdy in 3

  // Register write updates and no unintended writes
  assert property ( (drp_reg0_set || drp_reg1_set || drp_reg2_set || drp_reg3_set)
                    |=> (drp_register0_r == ($past(drp_reg0_set) ? $past(drp_di_r) : $past(drp_register0_r))) &&
                        (drp_register1_r == ($past(drp_reg1_set) ? $past(drp_di_r) : $past(drp_register1_r))) &&
                        (drp_register2_r == ($past(drp_reg2_set) ? $past(drp_di_r) : $past(drp_register2_r))) &&
                        (drp_register3_r == ($past(drp_reg3_set) ? $past(drp_di_r) : $past(drp_register3_r))) );

  // Read data muxing (next cycle after get)
  assert property ( drp_do ==
                   (($past(drp_reg0_get) ? $past(drp_register0_r) : 16'h0) |
                    ($past(drp_reg1_get) ? $past(drp_register1_r) : 16'h0) |
                    ($past(drp_reg2_get) ? $past(drp_register2_r) : 16'h0) |
                    ($past(drp_reg3_get) ? $past(drp_register3_r) : 16'h0)) );

  // Coverage: write & read each register; write-readback returns the same data
  cover property ((drp_en && drp_we && (drp_addr==DRP_REG0)) ##2 drp_rdy);
  cover property ((drp_en && drp_we && (drp_addr==DRP_REG1)) ##2 drp_rdy);
  cover property ((drp_en && drp_we && (drp_addr==DRP_REG2)) ##2 drp_rdy);
  cover property ((drp_en && drp_we && (drp_addr==DRP_REG3)) ##2 drp_rdy);

  cover property ((drp_en && !drp_we && (drp_addr==DRP_REG0)) ##3 drp_rdy);
  cover property ((drp_en && !drp_we && (drp_addr==DRP_REG1)) ##3 drp_rdy);
  cover property ((drp_en && !drp_we && (drp_addr==DRP_REG2)) ##3 drp_rdy);
  cover property ((drp_en && !drp_we && (drp_addr==DRP_REG3)) ##3 drp_rdy);

  // Per-register write->readback data integrity
  sequence wr_then_rd0(logic [15:0] d);
    (drp_en && drp_we && drp_addr==DRP_REG0, d=drp_di)
    ##3 (drp_en && !drp_we && drp_addr==DRP_REG0)
    ##3 (drp_rdy && drp_do==d);
  endsequence
  sequence wr_then_rd1(logic [15:0] d);
    (drp_en && drp_we && drp_addr==DRP_REG1, d=drp_di)
    ##3 (drp_en && !drp_we && drp_addr==DRP_REG1)
    ##3 (drp_rdy && drp_do==d);
  endsequence
  sequence wr_then_rd2(logic [15:0] d);
    (drp_en && drp_we && drp_addr==DRP_REG2, d=drp_di)
    ##3 (drp_en && !drp_we && drp_addr==DRP_REG2)
    ##3 (drp_rdy && drp_do==d);
  endsequence
  sequence wr_then_rd3(logic [15:0] d);
    (drp_en && drp_we && drp_addr==DRP_REG3, d=drp_di)
    ##3 (drp_en && !drp_we && drp_addr==DRP_REG3)
    ##3 (drp_rdy && drp_do==d);
  endsequence

  cover property (wr_then_rd0(d));
  cover property (wr_then_rd1(d));
  cover property (wr_then_rd2(d));
  cover property (wr_then_rd3(d));

endmodule

// Bind into DUT
bind drp_other_registers
  drp_other_registers_sva #(
    .DRP_ABITS(DRP_ABITS),
    .DRP_REG0 (DRP_REG0),
    .DRP_REG1 (DRP_REG1),
    .DRP_REG2 (DRP_REG2),
    .DRP_REG3 (DRP_REG3)
  ) i_drp_other_registers_sva (.*);