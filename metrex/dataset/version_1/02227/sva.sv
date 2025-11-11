// SVA for qmem_sram
// Concise, high-signal-quality checks and coverage
// Drop-in bind. Uses only DUT ports; no internal hierarchical refs.
// Mirrors DUT config macros for correct behavior mapping.

module qmem_sram_sva #(
  parameter AW = 32,
  parameter DW = 32,
  parameter SW = DW/8
)(
  input  wire           clk50,
  input  wire           clk100,
  input  wire           rst,
  input  wire [AW-1:0]  adr,
  input  wire           cs,
  input  wire           we,
  input  wire [SW-1:0]  sel,
  input  wire [DW-1:0]  dat_w,
  output wire [DW-1:0]  dat_r,
  output wire           ack,
  output wire           err,
  output wire [18-1:0]  sram_adr,
  output wire           sram_ce_n,
  output wire           sram_we_n,
  output wire           sram_ub_n,
  output wire           sram_lb_n,
  output wire           sram_oe_n,
  output wire [16-1:0]  sram_dat_w,
  input  wire [16-1:0]  sram_dat_r
);

`ifndef QMEM_SRAM_ASYNC
  default clocking cb @(posedge clk100); endclocking
`else
  default clocking cb @(posedge clk50 ); endclocking
`endif
  default disable iff (rst);

// Common sanity: err is always 0
assert property (cb !$isunknown(err) and (err == 1'b0));

// No X on key outputs when chip is selected
assert property (cb cs |-> !$isunknown({sram_ce_n,sram_we_n,sram_oe_n,sram_ub_n,sram_lb_n,sram_adr,sram_dat_w}));

// -------------- Config: SLOW/FAST (clk100 domain) --------------
`ifndef QMEM_SRAM_ASYNC

// When CE is active, WE_N/ OE_N must reflect WE
assert property (cb (sram_ce_n == 1'b0) |-> (sram_we_n == !we) and (sram_oe_n == we));

// Address LSB defines halfword; control and data mapping must match
// HI half (addr[0]==0) uses upper bytes [31:16]
assert property (cb (sram_ce_n==1'b0 && sram_adr[0]==1'b0) |->
                 (sram_dat_w == dat_w[31:16]) &&
                 ({sram_ub_n,sram_lb_n} == {!sel[3],!sel[2]}));
// LO half (addr[0]==1) uses lower bytes [15:0]
assert property (cb (sram_ce_n==1'b0 && sram_adr[0]==1'b1) |->
                 (sram_dat_w == dat_w[15:0]) &&
                 ({sram_ub_n,sram_lb_n} == {!sel[1],!sel[0]}));

// ack must only occur during a valid access window
assert property (cb ack |-> cs);

// FAST: ack is a single-cycle pulse and occurs on LO half
`ifndef QMEM_SRAM_SLOW
  assert property (cb $rose(ack) |-> ##1 !ack);
  assert property (cb ack |-> (sram_ce_n==1'b0 && sram_adr[0]==1'b1));
  // Ack requires cs to have been held at least one prior cycle
  assert property (cb ack |-> $past(cs));
  // Coverage: read then complete (two halves) with ack in middle
  cover property (cb cs && !we ##1 cs && !we && ack ##1 cs && !we);
  // Coverage: write two halves with ack in middle
  cover property (cb cs &&  we ##1 cs &&  we && ack);
`else
// SLOW: ack extends for two cycles across LO2 and FH
  assert property (cb $rose(ack) |-> ack ##1 ack ##2 !ack);
  // Coverage: read full two-half sequence with 2-cycle ack
  cover property (cb cs && !we ##1 cs && !we ##1 ack ##1 ack ##1 !ack);
  // Coverage: write two-half sequence with 2-cycle ack
  cover property (cb cs &&  we ##1 cs &&  we ##1 ack ##1 ack);
`endif

// -------------- Config: ASYNC (clk50 domain) --------------
`else

// In async build, CE and WE/OE are directly driven
assert property (cb (sram_ce_n == !cs));
assert property (cb (sram_we_n == !we));
assert property (cb (sram_oe_n == we));

// Mapping by half-cycle (addr[0] toggles across halves with cs)
// First half (addr[0]==0): low data half and low byte enables
assert property (cb (cs && sram_adr[0]==1'b0) |->
                 (sram_dat_w == dat_w[15:0]) &&
                 ({sram_ub_n,sram_lb_n} == {!sel[1],!sel[0]}));
// Second half (addr[0]==1): high data half and high byte enables
assert property (cb (cs && sram_adr[0]==1'b1) |->
                 (sram_dat_w == dat_w[31:16]) &&
                 ({sram_ub_n,sram_lb_n} == {!sel[3],!sel[2]}));

// Under cs, ack mirrors second-half (addr[0]) phase
assert property (cb cs |-> (ack == sram_adr[0]));

// Read data assembly check: on back-to-back halves with cs held and !we,
// the 32b dat_r equals {second_half, first_half}
sequence two_halves_read;
  cs && !we && (sram_adr[0]==1'b0) ##1 cs && !we && (sram_adr[0]==1'b1);
endsequence
assert property (cb two_halves_read |-> (dat_r == {sram_dat_r, $past(sram_dat_r)}));

// Coverage: read two halves
cover property (cb two_halves_read);
// Coverage: write two halves
cover property (cb cs && we && (sram_adr[0]==1'b0) ##1 cs && we && (sram_adr[0]==1'b1));

`endif

endmodule

// Bind to all qmem_sram instances
bind qmem_sram qmem_sram_sva #(.AW(AW), .DW(DW), .SW(SW)) qmem_sram_sva_b (.*);