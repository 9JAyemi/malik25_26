module internal_bank_address_sva (
    input logic        lio_buscfg_brstlen2_sr,
    input logic        lio_buscfg_brstlen4_sr,
    input logic [7:0]  m_cdq_haddr_sr,
    input logic [3:0]  ibnk_sel_s
);

    // Upper output bits are always zero because the RTL assigns a 2-bit slice to a 4-bit output.
    check_upper_bits_zero: assert property (
        @($global_clock) ibnk_sel_s[3:2] === 2'b00
    );

    // In 2-burst mode, the bank select comes from address bits [1:0].
    check_2burst_decode: assert property (
        @($global_clock)
        ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} === 2'b01)
        |-> (ibnk_sel_s === {2'b00, m_cdq_haddr_sr[1:0]})
    );

    // In 4-burst mode, the bank select comes from address bits [2:1].
    check_4burst_decode: assert property (
        @($global_clock)
        ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} === 2'b10)
        |-> (ibnk_sel_s === {2'b00, m_cdq_haddr_sr[2:1]})
    );

    // When both burst-length flags are low, the default decode uses address bits [2:1].
    check_default_decode_00: assert property (
        @($global_clock)
        ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} === 2'b00)
        |-> (ibnk_sel_s === {2'b00, m_cdq_haddr_sr[2:1]})
    );

    // When both burst-length flags are high, the default decode uses address bits [2:1].
    check_default_decode_11: assert property (
        @($global_clock)
        ({lio_buscfg_brstlen4_sr, lio_buscfg_brstlen2_sr} === 2'b11)
        |-> (ibnk_sel_s === {2'b00, m_cdq_haddr_sr[2:1]})
    );

endmodule