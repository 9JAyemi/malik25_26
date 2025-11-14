// SVA for dual_port_mem
// Place inside the module or bind to it. Uses internal ram_lb/ram_ub.

`ifndef SYNTHESIS
// Default clock for assertions
default clocking cb @(posedge clk_i); endclocking

// Structural read path must reflect memory bytes
a_read_path: assert property ({ram_ub[address_i], ram_lb[address_i]} === data_o);

// Control/data must be known when used
a_ctrl_known: assert property (wren_i |-> (!$isunknown(be_i) && !$isunknown(address_i)));
a_lb_data_known: assert property ((wren_i && (be_i==2'b00 || be_i==2'b01)) |-> !$isunknown(data_i[7:0]));
a_ub_data_known: assert property ((wren_i && (be_i==2'b00 || be_i==2'b10)) |-> !$isunknown(data_i[15:8]));

// No write when wren_i==0 (addressed location holds value)
a_no_write_when_wren0: assert property
  ((!wren_i) |=> (ram_lb[$past(address_i)] === $past(ram_lb[address_i]) &&
                  ram_ub[$past(address_i)] === $past(ram_ub[address_i])));

// Masked write (be_i==11) is a no-op
a_masked_noop: assert property
  ((wren_i && be_i==2'b11) |=> (ram_lb[$past(address_i)] === $past(ram_lb[address_i]) &&
                                ram_ub[$past(address_i)] === $past(ram_ub[address_i])));

// Full-word write (both bytes update)
a_full_write: assert property
  ((wren_i && be_i==2'b00) |=> (ram_lb[$past(address_i)] === $past(data_i[7:0]) &&
                                ram_ub[$past(address_i)] === $past(data_i[15:8])));

// Lower-byte-only write (upper byte unchanged)
a_lb_only_write: assert property
  ((wren_i && be_i==2'b01) |=> (ram_lb[$past(address_i)] === $past(data_i[7:0]) &&
                                ram_ub[$past(address_i)] === $past(ram_ub[address_i])));

// Upper-byte-only write (lower byte unchanged)
a_ub_only_write: assert property
  ((wren_i && be_i==2'b10) |=> (ram_ub[$past(address_i)] === $past(data_i[15:8]) &&
                                ram_lb[$past(address_i)] === $past(ram_lb[address_i])));

// Read-after-write observable effects when address is held
c_full_write_read: cover property
  ((wren_i && be_i==2'b00) ##1 (address_i == $past(address_i) && data_o === $past(data_i)));

c_lb_write_read: cover property
  ((wren_i && be_i==2'b01) ##1 (address_i == $past(address_i) &&
                                 data_o[7:0] === $past(data_i[7:0])));

c_ub_write_read: cover property
  ((wren_i && be_i==2'b10) ##1 (address_i == $past(address_i) &&
                                 data_o[15:8] === $past(data_i[15:8])));

c_masked_noop_read: cover property
  ((wren_i && be_i==2'b11) ##1 (address_i == $past(address_i) &&
                                 data_o === $past(data_o)));

// Address corner coverage
c_addr_lo: cover property (wren_i && (address_i == '0));
c_addr_hi: cover property (wren_i && (address_i == {SIZE{1'b1}}));
`endif