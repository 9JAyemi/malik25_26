// SVA for select_internal_bank_address_subfield
// Bind this module and drive 'clk' with a sampling clock.

module select_internal_bank_address_subfield_sva #(parameter int NumBnks = 4) (
  input logic clk,
  input logic lio_buscfg_brstlen2_sr,
  input logic lio_buscfg_brstlen4_sr,
  input logic [NumBnks-1:0] m_cdq_haddr_sr,
  input logic [NumBnks-1:0] ibnk_sel_s
);

  default clocking cb @(posedge clk); endclocking

  // Static parameter sanity
  initial assert (NumBnks >= 4)
    else $error("NumBnks(%0d) must be >= 4 for bit ranges [3:0]", NumBnks);

  // Helper: zero-extend 2-bit value to output width
  function automatic logic [NumBnks-1:0] zext2(input logic [1:0] v);
    logic [NumBnks-1:0] r; begin r = '0; r[1:0] = v; return r; end
  endfunction

  // Short-hands
  wire [1:0] haddr_bst2 = m_cdq_haddr_sr[1:0];
  wire [1:0] haddr_bst4 = m_cdq_haddr_sr[2:1];
  wire [1:0] haddr_bst8 = m_cdq_haddr_sr[3:2];
  wire [1:0] sel = {lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr};

  // 2-state select lines (no X/Z on control)
  a_sel_2state: assert property (!$isunknown(sel));

  // Used address bits must be known in each mode
  a_xfree_bst2: assert property (sel == 2'b01 |-> !$isunknown(haddr_bst2));
  a_xfree_bst4: assert property (sel == 2'b10 |-> !$isunknown(haddr_bst4));
  a_xfree_bst8: assert property ((sel != 2'b01 && sel != 2'b10) |-> !$isunknown(haddr_bst8));

  // Functional mapping
  a_map_bst2: assert property (sel == 2'b01 |-> ibnk_sel_s == zext2(haddr_bst2));
  a_map_bst4: assert property (sel == 2'b10 |-> ibnk_sel_s == zext2(haddr_bst4));
  a_map_def:  assert property ((sel != 2'b01 && sel != 2'b10) |-> ibnk_sel_s == zext2(haddr_bst8));

  // Width/placement: upper bits must always be zero
  a_upper_zero: assert property (ibnk_sel_s[NumBnks-1:2] == '0);

  // Stability: if controls and relevant bits are stable, output is stable
  a_stable_bst2: assert property (sel == 2'b01 && $stable({sel,haddr_bst2}) |-> $stable(ibnk_sel_s));
  a_stable_bst4: assert property (sel == 2'b10 && $stable({sel,haddr_bst4}) |-> $stable(ibnk_sel_s));
  a_stable_bst8: assert property (sel != 2'b01 && sel != 2'b10 && $stable({sel,haddr_bst8}) |-> $stable(ibnk_sel_s));

  // Coverage: exercise all modes and transitions
  c_mode_bst2:    cover property (sel == 2'b01);
  c_mode_bst4:    cover property (sel == 2'b10);
  c_mode_bst8_00: cover property (sel == 2'b00);
  c_mode_bst8_11: cover property (sel == 2'b11);

  c_2_to_4: cover property (sel == 2'b01 ##1 sel == 2'b10);
  c_4_to_8: cover property (sel == 2'b10 ##1 (sel != 2'b01 && sel != 2'b10));
  c_8_to_2: cover property ((sel != 2'b01 && sel != 2'b10) ##1 sel == 2'b01);

  // Coverage: propagation (relevant address bits change -> output changes)
  c_prop_bst2: cover property (sel == 2'b01 && $changed(haddr_bst2) && $changed(ibnk_sel_s));
  c_prop_bst4: cover property (sel == 2'b10 && $changed(haddr_bst4) && $changed(ibnk_sel_s));
  c_prop_bst8: cover property ((sel != 2'b01 && sel != 2'b10) && $changed(haddr_bst8) && $changed(ibnk_sel_s));

endmodule

// Example bind (edit clk connection as needed):
// bind select_internal_bank_address_subfield
//   select_internal_bank_address_subfield_sva #(.NumBnks(NumBnks)) u_sva (
//     .clk(tb_clk),
//     .lio_buscfg_brstlen2_sr(lio_buscfg_brstlen2_sr),
//     .lio_buscfg_brstlen4_sr(lio_buscfg_brstlen4_sr),
//     .m_cdq_haddr_sr(m_cdq_haddr_sr),
//     .ibnk_sel_s(ibnk_sel_s)
//   );