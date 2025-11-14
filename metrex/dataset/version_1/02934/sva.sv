// SVA checker for sparc_exu_ecc_dec
module sparc_exu_ecc_dec_sva (
  input logic [6:0]  q,
  input logic [63:0] e
);

  // Canonical truth-table the DUT implements: e[i] <-> (q == Q_PAT[i])
  localparam logic [6:0] Q_PAT [64] = '{
    7'd3,  7'd5,  7'd6,  7'd7,  7'd9,  7'd10, 7'd11, 7'd12,
    7'd13, 7'd14, 7'd15, 7'd17, 7'd18, 7'd19, 7'd20, 7'd21,
    7'd22, 7'd23, 7'd24, 7'd25, 7'd26, 7'd27, 7'd28, 7'd29,
    7'd30, 7'd31, 7'd33, 7'd34, 7'd35, 7'd36, 7'd37, 7'd38,
    7'd39, 7'd40, 7'd41, 7'd42, 7'd43, 7'd44, 7'd45, 7'd46,
    7'd47, 7'd48, 7'd49, 7'd50, 7'd51, 7'd52, 7'd53, 7'd54,
    7'd55, 7'd56, 7'd57, 7'd58, 7'd59, 7'd60, 7'd61, 7'd62,
    7'd63, 7'd65, 7'd66, 7'd67, 7'd68, 7'd69, 7'd70, 7'd71
  };

  function automatic void q_to_expected(
    input  logic [6:0]  qi,
    output logic        hit,
    output int          idx,
    output logic [63:0] e_exp
  );
    hit  = 1'b0;
    idx  = -1;
    e_exp = '0;
    for (int i = 0; i < 64; i++) begin
      if (qi == Q_PAT[i]) begin
        hit  = 1'b1;
        idx  = i;
        e_exp = 64'b1 << i;
        break;
      end
    end
  endfunction

  // Functional equivalence (full decode check) + onehot safety + X-prop safety
  always_comb begin
    logic        hit;
    int          idx;
    logic [63:0] e_exp;
    q_to_expected(q, hit, idx, e_exp);

    assert (e === e_exp)
      else $error("ecc_dec: e mismatch. q=%0d exp=%0h got=%0h idx=%0d hit=%0b", q, e_exp, e, idx, hit);

    assert ($onehot0(e))
      else $error("ecc_dec: e not onehot0. e=%0h q=%0d", e, q);

    if (!$isunknown(q)) assert (!$isunknown(e))
      else $error("ecc_dec: X/Z on e with known q. e=%0h q=%0d", e, q);
  end

  // Per-bit forward implication (redundant with e===e_exp but helpful for debug)
  generate
    for (genvar i = 0; i < 64; i++) begin : fwd_imp
      always_comb if (e[i]) assert (q == Q_PAT[i])
        else $error("ecc_dec: e[%0d]=1 but q!=Q_PAT. q=%0d expected %0d", i, q, Q_PAT[i]);
    end
  endgenerate

  // Coverage: hit every decoded output once; also see at least one "no-hit" case
  generate
    for (genvar i = 0; i < 64; i++) begin : cov_ei
      always_comb cover (q == Q_PAT[i] && e[i]);
    end
  endgenerate
  always_comb cover (e == '0); // input not in decode table

endmodule

// Bind example:
// bind sparc_exu_ecc_dec sparc_exu_ecc_dec_sva u_sva (.q(q), .e(e));