// SVA for sync_ram_wf_x32
module sync_ram_wf_x32_sva #(
  parameter ADDR_WIDTH = 10
)(
  input  logic              clk,
  input  logic [3:0]        web,
  input  logic [3:0]        enb,
  input  logic [9:0]        addr,
  input  logic [31:0]       din,
  input  logic [31:0]       dout,
  ref    logic [31:0]       RAM [(2<<ADDR_WIDTH)-1:0]
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X checks
  assert property (cb past_valid |-> !$isunknown({enb, web, addr, din}));

  genvar i;
  generate
    for (i=0; i<4; i++) begin : g
      localparam int L = 8*i;

      // When disabled, that byte of dout must hold its value
      assert property (cb !enb[i] |=> $stable(dout[L +: 8]));

      // Write: RAM byte updates at next cycle to written data
      assert property (cb disable iff (!past_valid)
        (enb[i] && web[i]) |-> ##1 (RAM[$past(addr)][L +: 8] == $past(din[L +: 8]))
      );

      // Write-first: dout reflects written data next cycle unless overwritten
      assert property (cb disable iff (!past_valid)
        (enb[i] && web[i]) |-> ##1 (enb[i] || (dout[L +: 8] == $past(din[L +: 8])))
      );

      // Read: dout gets stored data next cycle unless overwritten
      assert property (cb disable iff (!past_valid)
        (enb[i] && !web[i]) |-> ##1 (enb[i] || (dout[L +: 8] == $past(RAM[addr][L +: 8])))
      );

      // Read does not modify RAM
      assert property (cb disable iff (!past_valid)
        (enb[i] && !web[i]) |-> ##1 (RAM[$past(addr)][L +: 8] == $past(RAM[$past(addr)][L +: 8]))
      );

      // Addressed RAM byte only changes on an enabled write in prior cycle
      assert property (cb disable iff (!past_valid)
        (RAM[$past(addr)][L +: 8] != $past(RAM[$past(addr)][L +: 8]))
          |-> $past(enb[i] && web[i])
      );

      // If not enabled, addressed RAM byte must not change
      assert property (cb disable iff (!past_valid)
        !enb[i] |=> (RAM[$past(addr)][L +: 8] == $past(RAM[$past(addr)][L +: 8]))
      );

      // Coverage
      cover property (cb enb[i] && web[i]);                 // byte write
      cover property (cb enb[i] && !web[i]);                // byte read
      cover property (cb disable iff (!past_valid)
        (enb[i] && web[i]) ##1 (enb[i] && !web[i] && (addr == $past(addr)))
      );                                                   // RAW same address
    end
  endgenerate

  // Multi-byte coverage
  cover property (cb (enb == 4'hF && web == 4'hF));        // full 32-bit write
  cover property (cb (enb == 4'hF && web == 4'h0));        // full 32-bit read
  cover property (cb (enb == 4'hA && web == 4'hA));        // alternating bytes
  cover property (cb (enb == 4'h5 && web == 4'h5));

endmodule

bind sync_ram_wf_x32 sync_ram_wf_x32_sva #(.ADDR_WIDTH(ADDR_WIDTH)) u_sync_ram_wf_x32_sva
(
  .clk(clk),
  .web(web),
  .enb(enb),
  .addr(addr),
  .din(din),
  .dout(dout),
  .RAM(RAM)
);