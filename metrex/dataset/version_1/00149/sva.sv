// SystemVerilog Assertions for dm
// Bind-friendly checker; no DUT modifications required.
// Bind example (place in a package or a testbench file):
//   bind dm dm_sva dm_sva_i(.*);

module dm_sva(
  input logic        clk,
  input logic        rst,
  input logic        wr,
  input logic [6:0]  waddr,
  input logic [6:0]  raddr,
  input logic [31:0] wdata,
  input logic [31:0] rdata
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on active inputs/outputs
  property p_inputs_known;
    disable iff (!rst) !$isunknown({wr, waddr, raddr, wdata});
  endproperty
  assert property (p_inputs_known);

  property p_rdata_known;
    disable iff (!rst) !$isunknown(rdata);
  endproperty
  assert property (p_rdata_known);

  // Bus stability when sampling a write
  property p_write_stable_bus;
    disable iff (!rst) wr |-> $stable({waddr,wdata});
  endproperty
  assert property (p_write_stable_bus);

  // Next-cycle read-back of the just-written address
  property p_wr_rd_next;
    bit [6:0]   aw;
    bit [31:0]  dw;
    disable iff (!rst)
      (wr, aw=waddr, dw=wdata) ##1 (raddr==aw) |-> (rdata==dw);
  endproperty
  assert property (p_wr_rd_next);

  // Read-after-write correctness until rewritten (checked on every access)
  // If this address was the most recent write for that address, any read to it must return that data
  property p_read_sees_last_write_on_access;
    bit [6:0]   aw;
    bit [31:0]  dw;
    disable iff (!rst)
      (wr, aw=waddr, dw=wdata)
      |->
      ((raddr==aw) |-> (rdata==dw)) throughout (!wr || (waddr!=aw))[*0:$];
  endproperty
  assert property (p_read_sees_last_write_on_access);

  // Reset presets: after reset deasserts, when those locations are read soon, they return the preset values
  // (allows arbitrary time to the first read within 2 cycles; widen if your clock is very fast vs #1 in DUT)
  property p_reset_preset_20_readback;
    $rose(rst) ##[0:2] (raddr==7'd20) |-> (rdata==32'd10);
  endproperty
  assert property (p_reset_preset_20_readback);

  property p_reset_preset_21_readback;
    $rose(rst) ##[0:2] (raddr==7'd21) |-> (rdata==32'h3);
  endproperty
  assert property (p_reset_preset_21_readback);

  // Coverage
  cover property (@cb $fell(rst) ##[1:10] $rose(rst));                       // reset cycle
  cover property (@cb disable iff (!rst) wr);                                // any write
  cover property (@cb disable iff (!rst) wr ##1 (raddr==$past(waddr)));      // write then read same addr next
  cover property (@cb disable iff (!rst) wr && (waddr inside {7'd20,7'd21})); // write to preset locations

endmodule