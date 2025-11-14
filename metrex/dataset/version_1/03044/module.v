module select_internal_bank_address_subfield #(
    parameter NumBnks = 4 // Define NumBnks parameter
)(
  input lio_buscfg_brstlen2_sr,
  input lio_buscfg_brstlen4_sr,
  input [NumBnks-1:0] m_cdq_haddr_sr,
  output reg [NumBnks-1:0] ibnk_sel_s
);


  // Define ranges for bank address subfield based on burst length
  `define DMC_AG_HADDR_BADDR_BST2_RNG 1:0
  `define DMC_AG_HADDR_BADDR_BST4_RNG 2:1
  `define DMC_AG_HADDR_BADDR_BST8_RNG 3:2

  // Select internal bank address subfield based on burst length
  always @*
    case ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr})
      2'b01: // 2-burst
        ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST2_RNG];
      2'b10: // 4-burst
        ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST4_RNG];
      default: // 8-burst
        ibnk_sel_s = m_cdq_haddr_sr[`DMC_AG_HADDR_BADDR_BST8_RNG];
    endcase

endmodule