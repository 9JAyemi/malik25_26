// SVA for data_mem
// Bind this checker to the DUT instance(s)
bind data_mem data_mem_sva dm_sva();

module data_mem_sva;
  // Bound into data_mem: has visibility of clk, dm_ctrl_sig, mem_ctrl_addr, data_in, data_out, data_mem

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic protocol/X/range checks
  assert property (cb !$isunknown(dm_ctrl_sig));
  assert property (cb (dm_ctrl_sig inside {2'b00,2'b01}) |-> (!$isunknown(mem_ctrl_addr) && mem_ctrl_addr[0:23] == 24'd0));
  assert property (cb (dm_ctrl_sig == 2'b01) |-> !$isunknown(data_in));

  // Read: next-cycle data_out reflects prior memory at prior address
  assert property (cb past_valid && $past(dm_ctrl_sig)==2'b00
                   |-> data_out == $past(data_mem[$past(mem_ctrl_addr)]));

  // Write: next-cycle memory at prior address equals prior data_in
  assert property (cb past_valid && $past(dm_ctrl_sig)==2'b01
                   |-> data_mem[$past(mem_ctrl_addr)] == $past(data_in));

  // Write does not update data_out (holds value)
  assert property (cb past_valid && $past(dm_ctrl_sig)==2'b01
                   |-> data_out == $past(data_out));

  // Default: next-cycle data_out forced to zero
  assert property (cb past_valid && !$isunknown($past(dm_ctrl_sig))
                   && !($past(dm_ctrl_sig) inside {2'b00,2'b01})
                   |-> data_out == 128'd0);

  // No memory change at addressed location on read/default
  assert property (cb past_valid && $past(dm_ctrl_sig) inside {2'b00,2'b10,2'b11}
                   |-> data_mem[$past(mem_ctrl_addr)] == $past(data_mem[$past(mem_ctrl_addr)]));

  // Coverage
  cover property (cb dm_ctrl_sig==2'b01); // write
  cover property (cb dm_ctrl_sig==2'b00); // read
  cover property (cb !(dm_ctrl_sig inside {2'b00,2'b01})); // default

  // Read-after-write to same address with no intervening write to that address
  logic [31:0] addr;
  logic [127:0] wdata;
  cover property (cb
    (dm_ctrl_sig==2'b01, addr=mem_ctrl_addr, wdata=data_in)
    ##[1:$] (dm_ctrl_sig==2'b00 && mem_ctrl_addr==addr)
    |=> (data_out == wdata)
  );

  // Back-to-back writes to different addresses
  cover property (cb (dm_ctrl_sig==2'b01)
                     ##1 (dm_ctrl_sig==2'b01 && mem_ctrl_addr != $past(mem_ctrl_addr)));
endmodule