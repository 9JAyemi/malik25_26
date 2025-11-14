// SVA for sdram_interface
// Concise checks for reset, counter, register updates, address decode,
// control/output relationships, and essential coverage.

module sdram_if_sva #(
  parameter int ROW_BITS     = 13,
  parameter int COL_BITS     = 10,
  parameter int BANK_BITS    = 2,
  parameter int BA_BITS      = BANK_BITS + ROW_BITS,
  parameter int ADDR_BITS    = BA_BITS + COL_BITS,
  parameter int DATA_WIDTH   = 16,
  parameter int BURST_LENGTH = 4
)(
  // DUT ports
  input  logic                  clk,
  input  logic                  rst,
  input  logic [31:0]           addr,
  input  logic                  we,
  input  logic                  cs,
  inout  logic [15:0]           dq,
  output logic [1:0]            dqm,
  output logic [2:0]            ba,
  output logic                  ras,
  output logic                  cas,
  output logic                  cke,
  output logic                  clkout,
  output logic                  odt,
  output logic                  cds,
  inout  logic [15:0]           dqout,

  // DUT internals (bound by name)
  input  logic [ADDR_BITS-1:0]  address_reg,
  input  logic [DATA_WIDTH-1:0] data_in_reg,
  input  logic [DATA_WIDTH-1:0] data_out_reg,
  input  logic [2:0]            burst_count_reg,
  input  logic [1:0]            dqm_reg,
  input  logic [ROW_BITS-1:0]   row_addr,
  input  logic [COL_BITS-1:0]   col_addr,
  input  logic [BANK_BITS-1:0]  bank_addr,
  input  logic [BA_BITS-1:0]    ba_reg,
  input  logic                  ras_reg,
  input  logic                  cas_reg,
  input  logic                  cke_reg,
  input  logic                  clkout_reg,
  input  logic                  odt_reg,
  input  logic                  cds_reg,
  input  logic [DATA_WIDTH-1:0] dqout_reg
);

  default clocking cb @(posedge clk); endclocking
  // Use explicit disable iff per-assert for reset-sensitive checks.

  // Reset values
  assert property (@cb rst |=> address_reg==0 && data_in_reg==0 && data_out_reg==0
                            && burst_count_reg==0 && dqm_reg==2'b11);

  // Counter range and evolution
  assert property (@cb !rst |-> burst_count_reg < BURST_LENGTH);
  assert property (@cb disable iff (rst)
                   cs |=> burst_count_reg == (($past(burst_count_reg)==BURST_LENGTH-1) ? 0
                                                                                       : $past(burst_count_reg)+1));
  assert property (@cb disable iff (rst)
                   !cs |=> burst_count_reg == $past(burst_count_reg));

  // Register updates and holds
  assert property (@cb disable iff (rst)
                   cs |=> address_reg == $past(addr));
  assert property (@cb disable iff (rst)
                   !cs |=> address_reg == $past(address_reg));

  assert property (@cb disable iff (rst)
                   (cs && we) |=> data_in_reg == $past(dq));
  assert property (@cb disable iff (rst)
                   !(cs && we) |=> data_in_reg == $past(data_in_reg));

  assert property (@cb disable iff (rst)
                   (cs && $past(burst_count_reg)==0) |=> data_out_reg == $past(dqout));
  assert property (@cb disable iff (rst)
                   (!cs || $past(burst_count_reg)!=0) |=> data_out_reg == $past(data_out_reg));

  // DQM next-state and hold
  assert property (@cb disable iff (rst)
                   cs |=> dqm_reg == (($past(burst_count_reg)==0) ? 2'b11 : 2'b00));
  assert property (@cb disable iff (rst)
                   !cs |=> dqm_reg == $past(dqm_reg));

  // Address decoding
  assert property (@cb row_addr  == addr[COL_BITS+BANK_BITS+ROW_BITS-1 -: ROW_BITS]);
  assert property (@cb col_addr  == addr[COL_BITS-1:0]);
  assert property (@cb bank_addr == addr[ADDR_BITS-1 -: BANK_BITS]);
  assert property (@cb ba_reg    == {bank_addr, row_addr});

  // Outputs vs internal regs/functions
  assert property (@cb dqm   == dqm_reg);
  // ba is narrower than ba_reg in this RTL; check lower bits match
  assert property (@cb ba    == ba_reg[$bits(ba)-1:0]);

  assert property (@cb ras   == (burst_count_reg==0));
  assert property (@cb cas   == (burst_count_reg==0));
  assert property (@cb cke   == (burst_count_reg!=0));
  assert property (@cb odt   == (burst_count_reg==BURST_LENGTH-1));
  assert property (@cb cds   == ~cs);

  assert property (@cb dqout == dqout_reg);
  assert property (@cb dqout_reg == ((burst_count_reg==0) ? dq : data_out_reg));

  // Clock forwarding: check alignment on rising edge
  assert property (@cb clkout == 1'b1);
  assert property (@cb $past(clkout)==1'b0) else $error("clkout did not toggle with clk");

  // Basic X-checks on control/status outputs (exclude inouts)
  assert property (@cb disable iff (rst)
                   !$isunknown({dqm, ba, ras, cas, cke, clkout, odt, cds}));

  // Covers

  // Full 4-beat burst progression and wrap (assumes BURST_LENGTH==4)
  cover property (@cb disable iff (rst)
    cs && burst_count_reg==0 ##1
    cs && burst_count_reg==1 ##1
    cs && burst_count_reg==2 ##1
    cs && burst_count_reg==3 ##1
    cs && burst_count_reg==0);

  // Cover start-of-burst control states
  cover property (@cb disable iff (rst) cs && burst_count_reg==0 && ras && cas && !cke && dqm==2'b11);

  // Cover last beat with ODT
  cover property (@cb disable iff (rst) cs && burst_count_reg==BURST_LENGTH-1 && odt);

  // Cover write and read bursts starting at beat 0
  cover property (@cb disable iff (rst) cs && we  && burst_count_reg==0 ##1 cs && we);
  cover property (@cb disable iff (rst) cs && !we && burst_count_reg==0 ##1 cs && !we);

  // Address extremes while selected
  cover property (@cb disable iff (rst)
    cs && bank_addr=={BANK_BITS{1'b0}} && row_addr=={ROW_BITS{1'b0}} && col_addr=={COL_BITS{1'b0}});
  cover property (@cb disable iff (rst)
    cs && bank_addr=={BANK_BITS{1'b1}} && row_addr=={ROW_BITS{1'b1}} && col_addr=={COL_BITS{1'b1}});

endmodule

// Bind into all instances of sdram_interface. Port names match DUT members; .* will connect internals.
bind sdram_interface sdram_if_sva #(
  .ROW_BITS(ROW_BITS), .COL_BITS(COL_BITS), .BANK_BITS(BANK_BITS),
  .BA_BITS(BA_BITS), .ADDR_BITS(ADDR_BITS), .DATA_WIDTH(DATA_WIDTH),
  .BURST_LENGTH(BURST_LENGTH)
) sva_i (.*);