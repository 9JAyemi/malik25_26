// SVA for spi_master and spi_slave
// Bind-friendly checkers that reference internal regs for concise, high-quality checks.

module spi_master_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        mosi,
  input  logic        cs,
  input  logic        sck_div,
  input  logic [7:0]  shift_reg,
  input  logic [2:0]  bit_counter,
  input  logic        sck,
  input  logic        cs_n,
  input  logic        miso
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Reset values
  ap_rst_vals: assert property (@cb rst |-> (shift_reg==8'h00 && bit_counter==3'd0 && sck==1'b0 && cs_n==1'b1 && miso==1'b0));

  // sck must toggle every cycle
  ap_sck_toggle: assert property (@cb sck == ~$past(sck));

  // cs_n updates only on cycles with old sck==1; otherwise it holds
  ap_cs_track: assert property (@cb $past(sck) |-> cs_n == $past(cs));
  ap_cs_hold:  assert property (@cb !$past(sck) |-> cs_n == $past(cs_n));

  // Shift/counter update only when active edge qualifies (!cs_n && old sck==1)
  ap_shift_when_active: assert property (@cb
      ($past(sck) && !$past(cs_n))
      |-> ( shift_reg == { $past(mosi), $past(shift_reg[7:1]) }
            && bit_counter == ( $past(bit_counter)==3'd7 ? 3'd0 : $past(bit_counter)+3'd1 ) ));

  // No shift/counter change otherwise
  ap_no_shift_otherwise: assert property (@cb
      !($past(sck) && !$past(cs_n))
      |-> (shift_reg == $past(shift_reg) && bit_counter == $past(bit_counter)));

  // miso updates only on last-bit event; otherwise holds
  ap_miso_update_on_7: assert property (@cb
      ($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7) |-> miso == $past(shift_reg[0]));
  ap_miso_hold: assert property (@cb
      !($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7) |-> miso == $past(miso));

  // Minimal, meaningful coverage
  cp_master_cs_active: cover property (@cb !cs_n);
  cp_master_byte_done: cover property (@cb ($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7));
  cp_master_sck_runs:  cover property (@cb sck && !$stable(sck));
endmodule

bind spi_master spi_master_sva i_spi_master_sva (.*);


module spi_slave_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        miso,
  input  logic        cs,
  input  logic        sck_div,
  input  logic [7:0]  shift_reg,
  input  logic [2:0]  bit_counter,
  input  logic        sck,
  input  logic        cs_n,
  input  logic        mosi
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Reset values
  ap_rst_vals: assert property (@cb rst |-> (shift_reg==8'h00 && bit_counter==3'd0 && sck==1'b0 && cs_n==1'b1 && mosi==1'b0));

  // sck must toggle every cycle
  ap_sck_toggle: assert property (@cb sck == ~$past(sck));

  // cs_n updates only on cycles with old sck==1; otherwise it holds
  ap_cs_track: assert property (@cb $past(sck) |-> cs_n == $past(cs));
  ap_cs_hold:  assert property (@cb !$past(sck) |-> cs_n == $past(cs_n));

  // Shift/counter update only when active edge qualifies (!cs_n && old sck==1)
  ap_shift_when_active: assert property (@cb
      ($past(sck) && !$past(cs_n))
      |-> ( shift_reg == { $past(shift_reg[6:0]), $past(miso) }
            && bit_counter == ( $past(bit_counter)==3'd7 ? 3'd0 : $past(bit_counter)+3'd1 ) ));

  // No shift/counter change otherwise
  ap_no_shift_otherwise: assert property (@cb
      !($past(sck) && !$past(cs_n))
      |-> (shift_reg == $past(shift_reg) && bit_counter == $past(bit_counter)));

  // mosi updates only on last-bit event; otherwise holds
  ap_mosi_update_on_7: assert property (@cb
      ($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7) |-> mosi == $past(shift_reg[7]));
  ap_mosi_hold: assert property (@cb
      !($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7) |-> mosi == $past(mosi));

  // Minimal, meaningful coverage
  cp_slave_cs_active: cover property (@cb !cs_n);
  cp_slave_byte_done: cover property (@cb ($past(sck) && !$past(cs_n) && $past(bit_counter)==3'd7));
  cp_slave_sck_runs:  cover property (@cb sck && !$stable(sck));
endmodule

bind spi_slave spi_slave_sva i_spi_slave_sva (.*);