// SVA for ay_note_ram
// Provide clk/rst_n from your environment; bind example at bottom.

module ay_note_ram_sva(input logic clk, input logic rst_n);
  // Bound into ay_note_ram scope: can see addr, data, note_ram[]
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  ap_addr_known: assert property (disable iff (!rst_n) !$isunknown(addr));
  ap_data_known: assert property (disable iff (!rst_n) !$isunknown(data));

  // Combinational read correctness
  ap_comb_read:  assert property (disable iff (!rst_n) data == note_ram[addr]);

  // Stability with stable address
  ap_stable_when_addr_stable: assert property (disable iff (!rst_n) $stable(addr) |-> $stable(data));

  // ROM cells are initialized and never change after reset deassert
  genvar i;
  generate
    for (i = 0; i < 128; i++) begin : g_mem_invariant
      ap_cell_known:  assert property (disable iff (!rst_n) !$isunknown(note_ram[i]));
      ap_cell_stable: assert property (disable iff (!rst_n) $stable(note_ram[i]));
      ap_cell_range:  assert property (disable iff (!rst_n) note_ram[i] inside {[12'd9:12'd3977]});
    end

    // Shape checks on content (concise but strong)
    for (i = 0; i <= 21; i++) begin : g_head_constant
      ap_head_const: assert property (disable iff (!rst_n) note_ram[i] == 12'd3977);
    end
    for (i = 0; i < 127; i++) begin : g_monotone
      ap_nonincreasing: assert property (disable iff (!rst_n) note_ram[i+1] <= note_ram[i]);
    end
  endgenerate

  // Spot-check key entries
  ap_idx22:  assert property (disable iff (!rst_n) note_ram[22]  == 12'd3754);
  ap_last:   assert property (disable iff (!rst_n) note_ram[127] == 12'd9);

  // Address coverage: hit every entry at least once
  logic [127:0] seen;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) seen <= '0;
    else         seen[addr] <= 1'b1;
  end
  cp_all_addrs: cover property (disable iff (!rst_n) seen == {128{1'b1}});

  // Boundary covers
  cp_addr0:   cover property (disable iff (!rst_n) addr == 7'd0);
  cp_addr21:  cover property (disable iff (!rst_n) addr == 7'd21 && data == 12'd3977);
  cp_addr22:  cover property (disable iff (!rst_n) addr == 7'd22 && data == 12'd3754);
  cp_addr127: cover property (disable iff (!rst_n) addr == 7'd127 && data == 12'd9);

  // Cover the drop from 3977 to 3754 on consecutive cycles (typical boundary)
  cp_drop_21_to_22: cover property (disable iff (!rst_n)
    (addr == 7'd21 && data == 12'd3977) ##1 (addr == 7'd22 && data == 12'd3754));
endmodule

// Example bind (hook clk/rst_n from your TB/top)
// bind ay_note_ram ay_note_ram_sva u_ay_note_ram_sva(.clk(tb_clk), .rst_n(tb_rst_n));