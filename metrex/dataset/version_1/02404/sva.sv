// SVA for dffe: synchronous active-low clear/preset with enable
// Bindable checker module with concise, high-quality checks and coverage

module dffe_sva (
  input logic CLK,
  input logic D,
  input logic ENA,
  input logic CLRN,
  input logic PRN,
  input logic Q
);
  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Known-value checks (at active clock)
  ap_no_x_ctrl: assert property (past_valid |-> !$isunknown({CLRN,PRN,ENA,D}));
  ap_no_x_q:    assert property (past_valid |-> !$isunknown(Q));

  // Golden next-state function (priority: CLRN > PRN > ENA > hold)
  ap_next_state: assert property (
    past_valid |-> Q ==
      ( !$past(CLRN) ? 1'b0 :
        !$past(PRN)  ? 1'b1 :
         $past(ENA)  ? $past(D) :
                        $past(Q) )
  );

  // Any Q change must have a valid cause (clear/preset or enabled load with D!=Q)
  ap_change_cause: assert property (
    past_valid && (Q != $past(Q))
    |-> ( !$past(CLRN) || !$past(PRN) ||
          ( $past(CLRN) && $past(PRN) && $past(ENA) && ($past(D) != $past(Q)) ) )
  );

  // Targeted priority checks (redundant with ap_next_state but give clearer failures)
  ap_clear:  assert property (past_valid && !$past(CLRN)                   |-> Q==1'b0);
  ap_preset: assert property (past_valid &&  $past(CLRN) && !$past(PRN)    |-> Q==1'b1);
  ap_hold:   assert property (past_valid &&  $past(CLRN) &&  $past(PRN) &&
                                            !$past(ENA)                    |-> Q==$past(Q));
  ap_load:   assert property (past_valid &&  $past(CLRN) &&  $past(PRN) &&
                                             $past(ENA)                    |-> Q==$past(D));

  // Optional: initial state from RTL init
  initial ap_init_q0: assert (Q === 1'b0);

  // Coverage: exercise all behaviors
  cp_clear:       cover property (past_valid && !$past(CLRN));
  cp_preset:      cover property (past_valid &&  $past(CLRN) && !$past(PRN));
  cp_hold:        cover property (past_valid &&  $past(CLRN) &&  $past(PRN) && !$past(ENA));
  cp_en_load_0to1:cover property (past_valid &&  $past(CLRN) &&  $past(PRN) &&
                                             $past(ENA) && !$past(Q) && $past(D));
  cp_en_load_1to0:cover property (past_valid &&  $past(CLRN) &&  $past(PRN) &&
                                             $past(ENA) &&  $past(Q) && !$past(D));
  cp_both_low:    cover property (past_valid && !$past(CLRN) && !$past(PRN));
endmodule

// Bind into DUT
bind dffe dffe_sva u_dffe_sva (.CLK(CLK), .D(D), .ENA(ENA), .CLRN(CLRN), .PRN(PRN), .Q(Q));