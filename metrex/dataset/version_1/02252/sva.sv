// SVA checker for dff_asr_en
module dff_asr_en_sva (
  input logic CLK, D, SET, RESET, EN,
  input logic Q, QN
);

  // Complement output must mirror Q
  assert property (@(posedge CLK) QN === ~Q)
    else $error("QN is not complement of Q");

  // When disabled, state must hold (guard first sample with $past known)
  assert property (@(posedge CLK) (!EN && !$isunknown($past(Q))) |-> ##0 (Q == $past(Q)))
    else $error("Q changed while EN=0");

  // SET has priority (also covers SET&RESET=1 -> Q=1)
  assert property (@(posedge CLK) (EN && SET) |-> ##0 (Q == 1'b1))
    else $error("SET did not force Q=1 when EN=1");

  // RESET when only RESET asserted
  assert property (@(posedge CLK) (EN && !SET && RESET) |-> ##0 (Q == 1'b0))
    else $error("RESET did not force Q=0 when EN=1 and SET=0");

  // Data capture when both SET/RESET deasserted
  assert property (@(posedge CLK) (EN && !SET && !RESET && !$isunknown($past(D))) |-> ##0 (Q == $past(D)))
    else $error("Q did not capture D when EN=1 and SET=RESET=0");

  // Controls must be known when used
  assert property (@(posedge CLK) EN |-> !$isunknown({SET,RESET}))
    else $error("SET/RESET unknown while EN=1");

  // D must be known when it is sampled
  assert property (@(posedge CLK) (EN && !SET && !RESET) |-> !$isunknown($past(D)))
    else $error("D unknown at sampling when EN=1 and SET=RESET=0");

  // -------------------
  // Functional coverage
  // -------------------
  // Cover SET only
  cover property (@(posedge CLK) EN && SET && !RESET ##0 (Q == 1'b1));

  // Cover RESET only
  cover property (@(posedge CLK) EN && !SET && RESET ##0 (Q == 1'b0));

  // Cover both SET and RESET asserted (SET priority)
  cover property (@(posedge CLK) EN && SET && RESET ##0 (Q == 1'b1));

  // Cover data capture 0->1 and 1->0 transitions
  cover property (@(posedge CLK) EN && !SET && !RESET && !$isunknown($past(D)) && ($past(D) != $past(Q)) ##0 (Q == $past(D)));
  cover property (@(posedge CLK) $rose(Q));
  cover property (@(posedge CLK) $fell(Q));

  // Cover hold while disabled
  cover property (@(posedge CLK) !EN && !$isunknown($past(Q)) ##0 (Q == $past(Q)));

  // Cover that EN gates over asserted controls
  cover property (@(posedge CLK) !EN && (SET || RESET) ##0 (Q == $past(Q)));

endmodule

// Bind into the DUT
bind dff_asr_en dff_asr_en_sva i_dff_asr_en_sva (.*);