// SVA bind module for "memory". Concise checks for connectivity, polarity, and write behavior.
module memory_sva #(parameter ADDR_W=19, DATA_W=36)
(
  input clk,
  input cen,
  input we,
  input [ADDR_W-1:0] addr,
  input [DATA_W-1:0] write_data,
  input [DATA_W-1:0] read_data,
  input ram_clk,
  input ram_we_b,
  input [ADDR_W-1:0] ram_address,
  input [DATA_W-1:0] ram_data,
  input ram_cen_b
);

  default clocking cb @(posedge clk); endclocking

  // Avoid time-0 $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Connectivity and polarity
  a_cen_pol:  assert property (disable iff(!past_valid) ram_cen_b == ~cen);
  a_we_pol:   assert property (disable iff(!past_valid) ram_we_b  == ~we);
  a_addr_map: assert property (disable iff(!past_valid) ram_address == addr);
  a_read_map: assert property (disable iff(!past_valid) read_data == ram_data);
  a_clk_const:assert property (ram_clk == 1'b0);

  // Write behavior: only updates on cen && we, and value written matches write_data
  a_write_updates_data:
    assert property (disable iff(!past_valid) (cen && we) |=> ram_data == $past(write_data));

  a_no_write_stable:
    assert property (disable iff(!past_valid) (!(cen && we)) |=> $stable(ram_data));

  // Any observed change must be caused by a prior-cycle write enable under cen
  a_change_implies_write:
    assert property (disable iff(!past_valid) (ram_data != $past(ram_data)) |-> $past(cen && we));

  // Read reflects last written data on the following cycle
  a_read_after_write:
    assert property (disable iff(!past_valid) (cen && we) |=> read_data == $past(write_data));

  // Basic covers
  c_one_write:         cover property (disable iff(!past_valid) (cen && we) ##1 (ram_data == $past(write_data)));
  c_back_to_back:      cover property (disable iff(!past_valid) (cen && we) ##1 (cen && we));
  c_long_idle:         cover property (disable iff(!past_valid) (!(cen && we)) [*3]);

endmodule

// Bind into the DUT
bind memory memory_sva #(.ADDR_W(19), .DATA_W(36)) u_memory_sva
(
  .clk(clk),
  .cen(cen),
  .we(we),
  .addr(addr),
  .write_data(write_data),
  .read_data(read_data),
  .ram_clk(ram_clk),
  .ram_we_b(ram_we_b),
  .ram_address(ram_address),
  .ram_data(ram_data),
  .ram_cen_b(ram_cen_b)
);