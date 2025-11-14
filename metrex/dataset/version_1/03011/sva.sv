// SVA for encode_8b10b
// Concise, white-box equivalence + key protocol checks + functional coverage.
// Bind into DUT and drive clk/rst_n from your env.

module encode_8b10b_sva (
  input  logic              clk,
  input  logic              rst_n,
  // DUT ports
  input  logic [8:0]        datain,
  input  logic              dispin,
  input  logic [9:0]        dataout,
  input  logic              dispout
);

  default clocking cb @(posedge clk); endclocking

  // Recompute DUT combinational spec (from inputs only)
  // Bit extracts
  logic ai,bi,ci,di,ei,fi,gi,hi,ki;
  always_comb begin
    ai = datain[0]; bi = datain[1]; ci = datain[2]; di = datain[3];
    ei = datain[4]; fi = datain[5]; gi = datain[6]; hi = datain[7];
    ki = datain[8];
  end

  // Lower 5b/6b precompute
  logic aeqb, ceqd, l22, l40, l04, l13, l31;
  always_comb begin
    aeqb = (ai & bi) | (!ai & !bi);
    ceqd = (ci & di) | (!ci & !di);
    l22  = (ai & bi & !ci & !di) |
           (ci & di & !ai & !bi) |
           (!aeqb & !ceqd);
    l40  = ai & bi & ci & di;
    l04  = !ai & !bi & !ci & !di;
    l13  = (!aeqb & !ci & !di) |
           (!ceqd & !ai & !bi);
    l31  = (!aeqb &  ci &  di) |
           (!ceqd &  ai &  bi);
  end

  // 6b pre-outputs
  logic ao,bo,co,do,eo,io;
  always_comb begin
    ao = ai;
    bo = (bi & !l40) | l04;
    co = l04 | ci | (ei & di & !ci & !bi & !ai);
    do = di & !(ai & bi & ci);
    eo = (ei | l13) & !(ei & di & !ci & !bi & !ai);
    io = (l22 & !ei) |
         (ei & !di & !ci & !(ai & bi)) | (ei & l40) |
         (ki & ei & di & ci & !bi & !ai) |
         (ei & !di & ci & !bi & !ai);
  end

  // 6b disparity helpers
  logic pd1s6, nd1s6, ndos6, pdos6;
  always_comb begin
    pd1s6 = (ei & di & !ci & !bi & !ai) | (!ei & !l22 & !l31);
    nd1s6 = ki | (ei & !l22 & !l13) | (!ei & !di & ci & bi & ai);
    ndos6 = pd1s6;
    pdos6 = ki | (ei & !l22 & !l13);
  end

  // 4b pre-outputs
  logic alt7, fo, go, ho, jo;
  always_comb begin
    alt7 = fi & gi & hi & (ki | (dispin ? (!ei & di & l31) : (ei & !di & l13)));
    fo   = fi & !alt7;
    go   = gi | (!fi & !gi & !hi);
    ho   = hi;
    jo   = (!hi & (gi ^ fi)) | alt7;
  end

  // 4b disparity helpers
  logic nd1s4, pd1s4, ndos4, pdos4;
  always_comb begin
    nd1s4 = fi & gi;
    pd1s4 = (!fi & !gi) | (ki & ((fi & !gi) | (!fi & gi)));
    ndos4 = (!fi & !gi);
    pdos4 = fi & gi & hi;
  end

  // Complements and outputs
  logic compls6, compls4, exp_dispout;
  logic [9:0] exp_dataout;
  logic       disp6;
  always_comb begin
    compls6    = (pd1s6 & !dispin) | (nd1s6 & dispin);
    disp6      = dispin ^ (ndos6 | pdos6);
    compls4    = (pd1s4 & !disp6) | (nd1s4 & disp6);
    exp_dispout = disp6 ^ (ndos4 | pdos4);

    exp_dataout = { (jo ^ compls4), (ho ^ compls4),
                    (go ^ compls4), (fo ^ compls4),
                    (io ^ compls6), (eo ^ compls6),
                    (do ^ compls6), (co ^ compls6),
                    (bo ^ compls6), (ao ^ compls6) };
  end

  // Helper: disparity of a 10b symbol: -2, 0, or +2 for valid 8b10b codes
  function automatic int signed disp_delta10 (logic [9:0] x);
    return int'(2*$countones(x)) - 10;
  endfunction

  // Assertions
  // No X/Z on outputs when inputs are known
  a_no_x: assert property (disable iff(!rst_n)
    !$isunknown({datain,dispin}) |-> !$isunknown({dataout,dispout})
  );

  // Exact combinational equivalence to spec
  a_match_do: assert property (disable iff(!rst_n)
    !$isunknown({datain,dispin}) |-> (dataout == exp_dataout)
  );
  a_match_disp: assert property (disable iff(!rst_n)
    !$isunknown({datain,dispin}) |-> (dispout == exp_dispout)
  );

  // DC-balance property of 8b/10b code group: disparity is in {-2,0,+2}
  a_dc_bal: assert property (disable iff(!rst_n)
    (disp_delta10(dataout) == -2) || (disp_delta10(dataout) == 0) || (disp_delta10(dataout) == 2)
  );

  // Neutral code groups hold running disparity
  a_neutral_rd_holds: assert property (disable iff(!rst_n)
    (disp_delta10(dataout) == 0) |-> (dispout == dispin)
  );

  // Coverage (functional touchpoints)
  // Stimulus hit both K and D paths
  c_ki0: cover property (disable iff(!rst_n) ki == 1'b0);
  c_ki1: cover property (disable iff(!rst_n) ki == 1'b1);

  // Alt7 path exercised
  c_alt7: cover property (disable iff(!rst_n) alt7);

  // Complement paths toggled
  c_compls6_0: cover property (disable iff(!rst_n) compls6 == 1'b0);
  c_compls6_1: cover property (disable iff(!rst_n) compls6 == 1'b1);
  c_compls4_0: cover property (disable iff(!rst_n) compls4 == 1'b0);
  c_compls4_1: cover property (disable iff(!rst_n) compls4 == 1'b1);

  // Disparity transitions
  c_disp_hold: cover property (disable iff(!rst_n) dispout == dispin);
  c_disp_flip: cover property (disable iff(!rst_n) dispout != dispin);

  // Code-group disparity bins
  c_delta_m2: cover property (disable iff(!rst_n) disp_delta10(dataout) == -2);
  c_delta_0 : cover property (disable iff(!rst_n) disp_delta10(dataout) == 0);
  c_delta_p2: cover property (disable iff(!rst_n) disp_delta10(dataout) == 2);

  // Internal steering events
  c_ndos6: cover property (disable iff(!rst_n) (ndos6 | pdos6));
  c_ndos4: cover property (disable iff(!rst_n) (ndos4 | pdos4));

  // Illegal K coverage (from spec expression)
  logic illegalk;
  always_comb begin
    illegalk = ki &
               (ai | bi | !ci | !di | !ei) &
               (!fi | !gi | !hi | !ei | !l31);
  end
  c_illegal_k: cover property (disable iff(!rst_n) illegalk);

endmodule

// Example bind (edit clk/rst to your env):
// bind encode_8b10b encode_8b10b_sva u_encode_8b10b_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));