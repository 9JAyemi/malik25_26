// SVA checker for internal_bank_address
// Bind example:
// bind internal_bank_address internal_bank_address_sva i_internal_bank_address_sva (.*);

module internal_bank_address_sva (
  input  logic        lio_buscfg_brstlen2_sr,
  input  logic        lio_buscfg_brstlen4_sr,
  input  logic [7:0]  m_cdq_haddr_sr,
  input  logic [3:0]  ibnk_sel_s
);

  // Invariants
  always_comb begin
    // Upper bits must be zero-extended by design
    assert (ibnk_sel_s[3:2] == 2'b00)
      else $error("ibnk_sel_s[3:2] must be 0");

    // If inputs are known, output must be known
    if (!$isunknown({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr, m_cdq_haddr_sr}))
      assert (!$isunknown(ibnk_sel_s))
        else $error("ibnk_sel_s has X/Z with known inputs");
  end

  // Functional mapping checks (combinational)
  always_comb begin
    unique case ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr})
      2'b01: begin // 2-burst
        assert (ibnk_sel_s[1:0] == m_cdq_haddr_sr[1:0])
          else $error("2-burst: ibnk_sel_s != haddr[1:0]");
      end
      2'b10: begin // 4-burst
        assert (ibnk_sel_s[1:0] == m_cdq_haddr_sr[2:1])
          else $error("4-burst: ibnk_sel_s != haddr[2:1]");
      end
      default: begin // 8-burst or conflicting (00 or 11) treated same
        assert (ibnk_sel_s[1:0] == m_cdq_haddr_sr[2:1])
          else $error("default: ibnk_sel_s != haddr[2:1]");
      end
    endcase
  end

  // Minimal but meaningful coverage
  always_comb begin
    // Cover each config
    cover ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b01);
    cover ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b10);
    cover ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b00);
    cover ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b11); // conflicting config seen

    // For each effective mapping, see low and high decoded values
    cover (({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b01) && (m_cdq_haddr_sr[1:0] == 2'b00));
    cover (({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b01) && (m_cdq_haddr_sr[1:0] == 2'b11));
    cover (({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b10) && (m_cdq_haddr_sr[2:1] == 2'b00));
    cover (({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} == 2'b10) && (m_cdq_haddr_sr[2:1] == 2'b11));
    cover (({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} != 2'b01 &&
            {lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} != 2'b10) &&
            (m_cdq_haddr_sr[2:1] == 2'b11));
  end

endmodule