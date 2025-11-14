// Bindable SystemVerilog Assertions for axi_crossbar_v2_1_10_addr_arbiter
// Quality-focused, concise checks + key coverage

bind axi_crossbar_v2_1_10_addr_arbiter axi_crossbar_v2_1_10_addr_arbiter_sva();

module axi_crossbar_v2_1_10_addr_arbiter_sva;

  // Use DUT’s clock/reset directly
  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // ----------
  // Basic protocol/encoding
  // ----------
  // Ready is one-hot-or-zero
  assert property ($onehot0(S_READY));

  // VALID holds until READY
  assert property (M_VALID && !M_READY |=> M_VALID);

  // On VALID stretch, outputs and encoding are stable
  assert property (M_VALID && !M_READY |=> $stable(M_GRANT_ENC) && $stable(M_MESG) && $stable(M_TARGET_HOT));

  // READY only on the first cycle of a VALID burst
  assert property ((|S_READY) |-> (M_VALID && !$past(M_VALID)));

  // READY bit matches grant encoding
  genvar gi_rdy;
  generate
    for (gi_rdy = 0; gi_rdy < C_NUM_S; gi_rdy++) begin : g_rdy_enc_chk
      assert property (S_READY[gi_rdy] |-> (M_GRANT_ENC == gi_rdy[C_NUM_S_LOG-1:0]));
    end
  endgenerate

  // During VALID (while waiting), grant_hot stays stable and correctly encodes index
  genvar gi_gh;
  generate
    for (gi_gh = 0; gi_gh < C_NUM_S; gi_gh++) begin : g_grant_hot_enc
      assert property (M_VALID && !M_READY && grant_hot[gi_gh] |-> (M_GRANT_ENC == gi_gh[C_NUM_S_LOG-1:0]));
    end
  endgenerate

  // ----------
  // Data/target capture behavior at grant
  // ----------
  // On the cycle READY pulses for i, TARGET_HOT matches the previous cycle’s source slice
  genvar gi_th;
  generate
    for (gi_th = 0; gi_th < C_NUM_S; gi_th++) begin : g_target_match
      assert property (S_READY[gi_th] |-> (M_TARGET_HOT == $past(S_TARGET_HOT[gi_th*C_NUM_M +: C_NUM_M])));
    end
  endgenerate

  // On VALID rise, M_MESG equals the pre-VALID muxed value and stays stable until handshake
  assert property ($rose(M_VALID) |-> (M_MESG == $past(m_mesg_mux)));
  assert property (M_VALID && !M_READY |=> $stable(M_MESG));

  // ----------
  // Qualifier and combinational definitions
  // ----------
  // valid_qual_i definition
  genvar gi_vq;
  generate
    for (gi_vq = 0; gi_vq < C_NUM_S; gi_vq++) begin : g_valid_qual_def
      assert property (valid_qual_i[gi_vq] == (S_VALID_QUAL[gi_vq] & (|(S_TARGET_HOT[gi_vq*C_NUM_M +: C_NUM_M] & ~ISSUING_LIMIT))));
    end
  endgenerate

  // qual_reg flops valid_qual_i | ~S_VALID
  assert property (qual_reg == $past(valid_qual_i | ~S_VALID));

  // ----------
  // Arbitration internal correctness (multi-source only)
  // ----------
  if (C_NUM_S > 1) begin : g_multi

    // valid_rr definition
    assert property (valid_rr == (~P_PRIO_MASK & S_VALID & ~s_ready_i & qual_reg));

    // Round-robin candidate must be one-hot-or-zero and subset of valid_rr
    assert property (found_rr |-> ($onehot(next_rr_hot) && ((next_rr_hot & ~valid_rr) == '0)));

    // Priority path signals well-formed
    assert property (found_prio |-> $onehot(next_prio_hot));
    assert property (prio_stall |-> !found_prio);

    // next_hot/next_enc consistency
    assert property (found_prio |-> (next_hot == next_prio_hot && next_enc == next_prio_enc));
    assert property (!found_prio && found_rr |-> (next_hot == next_rr_hot && next_enc == next_rr_enc));

    // When a grant is accepted (qualified and no stall), capture matches selection immediately
    assert property (((found_prio || found_rr) && !prio_stall && (|(next_hot & valid_qual_i)))
                     |-> (any_grant && grant_hot == next_hot && m_grant_enc_i == next_enc));

    // RR pointer advances only on RR grant
    assert property (((found_rr && !found_prio) && !prio_stall && (|(next_hot & valid_qual_i)))
                     |=> (last_rr_hot == $past(next_rr_hot)));

    // On VALID rise, READY equals grant_hot of that cycle
    assert property ($rose(M_VALID) |-> (S_READY == grant_hot));
  end

  // ----------
  // Coverage
  // ----------
  // Handshake with backpressure
  cover property ($rose(M_VALID) ##1 !M_READY ##[1:8] M_READY);

  // One grant observed for each source
  genvar gi_cov;
  generate
    for (gi_cov = 0; gi_cov < C_NUM_S; gi_cov++) begin : g_cov_per_src
      cover property (S_READY[gi_cov]);
    end
  endgenerate

  // Priority grant taken
  if (C_NUM_S > 1) begin
    cover property (found_prio && (|(next_prio_hot & valid_qual_i)) && !prio_stall ##1 M_VALID);
    // RR grant taken
    cover property (!found_prio && found_rr && (|(next_rr_hot & valid_qual_i)) ##1 M_VALID);
    // Priority stall observed
    cover property (prio_stall);
  end

endmodule