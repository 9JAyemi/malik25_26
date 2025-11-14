// SVA for gpio_wb: concise, high-quality protocol and data-path checks + coverage
module gpio_wb_sva #(parameter BASE_ADDR = 32'h00000400) (
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic [31:0] dat_i,
  input  logic [31:0] adr_i,
  input  logic        we_i,
  input  logic [3:0]  sel_i,
  input  logic        cyc_i,
  input  logic        stb_i,
  input  logic [15:0] sw_bi,
  input  logic [31:0] dat_o,
  input  logic        ack_o,
  input  logic [15:0] gpio_bo
);

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Local transaction qualifiers
  let rd = cyc_i && stb_i && !we_i;
  let wr = cyc_i && stb_i &&  we_i;

  // "Accepted" means request occurred while FSM was in IDLE (ack_o was 0 last cycle)
  let acc_rd = $past(!ack_o) && rd;
  let acc_wr = $past(!ack_o) && wr;

  // Asynchronous reset values must take effect when rst_i rises
  // (checks combinationally at reset edge)
  assert property (@(posedge rst_i) (ack_o==1'b0 && dat_o==32'h0 && gpio_bo==16'h0));

  // Handshake timing
  // Accepted READ: no same-cycle ack, 1-cycle-later ack
  assert property (acc_rd |-> (!ack_o && ##1 ack_o));

  // Accepted WRITE: same-cycle ack and next-cycle ack (stretch = 2)
  assert property (acc_wr |-> (ack_o && ##1 ack_o));

  // Data path on READ
  // Hit: return sw_bi (zero-extended) sampled at request cycle, when ack asserts
  assert property (acc_rd && (adr_i==BASE_ADDR)
                   |-> ##1 (ack_o && dat_o[15:0]==$past(sw_bi) && dat_o[31:16]==16'h0));

  // Miss: return zero when ack asserts
  assert property (acc_rd && (adr_i!=BASE_ADDR)
                   |-> ##1 (ack_o && dat_o==32'h0));

  // GPIO update on WRITE
  // Hit: update gpio_bo to dat_i[15:0] (visible next cycle)
  assert property (acc_wr && (adr_i==BASE_ADDR)
                   |-> ##1 (gpio_bo == $past(dat_i[15:0])));

  // Miss: gpio_bo must not change
  assert property (acc_wr && (adr_i!=BASE_ADDR)
                   |-> ##1 $stable(gpio_bo));

  // Writes must not affect dat_o
  assert property (acc_wr |-> ##1 $stable(dat_o));

  // Reads must not affect gpio_bo
  assert property (acc_rd |-> ##1 $stable(gpio_bo));

  // No X on key outputs (outside reset)
  assert property (!$isunknown({ack_o, dat_o, gpio_bo})));

  // --------------- Coverage ---------------

  // Reset observed
  cover property (@(posedge rst_i) 1);

  // Read-hit and data returned
  cover property (acc_rd && adr_i==BASE_ADDR ##1 (ack_o && dat_o[15:0]==$past(sw_bi)));

  // Read-miss returning zero
  cover property (acc_rd && adr_i!=BASE_ADDR ##1 (ack_o && dat_o==32'h0));

  // Write-hit updating gpio
  cover property (acc_wr && adr_i==BASE_ADDR ##1 (gpio_bo == $past(dat_i[15:0])));

  // Write-miss (no gpio change)
  cover property (acc_wr && adr_i!=BASE_ADDR ##1 $stable(gpio_bo));

  // Ack stretch on write (two consecutive ack cycles)
  cover property (acc_wr ##1 ack_o);

  // Sustained ack >=3 cycles (write, ack, then another write 2 cycles later)
  cover property (ack_o ##1 ack_o ##1 ack_o);

  // Read followed by write (basic mixed traffic)
  cover property (acc_rd ##2 acc_wr);

endmodule

// Bind into DUT
bind gpio_wb gpio_wb_sva #(.BASE_ADDR(BASE_ADDR)) u_gpio_wb_sva (
  .clk_i, .rst_i, .dat_i, .adr_i, .we_i, .sel_i, .cyc_i, .stb_i, .sw_bi, .dat_o, .ack_o, .gpio_bo
);