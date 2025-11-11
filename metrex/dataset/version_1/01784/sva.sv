// SVA for EHR_5: concise, high-quality checks and coverage
// Bind into the DUT so we can see internal r without changing RTL.
bind EHR_5 EHR_5_sva #(.DATA_SZ(DATA_SZ), .RESET_VAL(RESET_VAL)) i_ehr5_sva ();

module EHR_5_sva #(
  parameter int DATA_SZ = 1,
  parameter logic [DATA_SZ-1:0] RESET_VAL = '0
) ();

  default clocking cb @(posedge CLK); endclocking

  // Combinational read-path equivalence (disabled during reset)
  assert property (disable iff (!RST_N)) (read_0 == r);
  assert property (disable iff (!RST_N)) (read_1 == (EN_write_0 ? write_0 : r));
  assert property (disable iff (!RST_N)) (read_2 == (EN_write_1 ? write_1 : (EN_write_0 ? write_0 : r)));
  assert property (disable iff (!RST_N)) (read_3 == (EN_write_2 ? write_2 : (EN_write_1 ? write_1 : (EN_write_0 ? write_0 : r))));
  assert property (disable iff (!RST_N)) (read_4 == (EN_write_3 ? write_3 : (EN_write_2 ? write_2 : (EN_write_1 ? write_1 : (EN_write_0 ? write_0 : r)))));

  // Next-state update of r (synchronous active-low reset, write priority EN4..EN0)
  assert property (disable iff (!RST_N))
    ( r ==
      ( $past(RST_N) ?
          ( $past(EN_write_4) ? $past(write_4) :
            $past(EN_write_3) ? $past(write_3) :
            $past(EN_write_2) ? $past(write_2) :
            $past(EN_write_1) ? $past(write_1) :
            $past(EN_write_0) ? $past(write_0) :
            $past(r)
          )
        : RESET_VAL ) );

  // Hold when no writes enabled
  assert property (disable iff (!RST_N))
    ( !$past(EN_write_4|EN_write_3|EN_write_2|EN_write_1|EN_write_0) |-> r == $past(r) );

  // Reset behavior (must not be disabled)
  assert property ( !RST_N |-> ##1 r == RESET_VAL );

  // Known-ness in active mode
  assert property (RST_N |-> !$isunknown({EN_write_4,EN_write_3,EN_write_2,EN_write_1,EN_write_0}));
  assert property (RST_N |-> !$isunknown(r));
  assert property (RST_N |-> !$isunknown({read_4,read_3,read_2,read_1,read_0}));

  // Coverage: reset edges
  cover property ($rose(RST_N));
  cover property ($fell(RST_N));

  // Coverage: each priority level wins the update to r
  cover property ( $past(RST_N) && $past(EN_write_4)                                                 && r == $past(write_4) );
  cover property ( $past(RST_N) && !$past(EN_write_4) && $past(EN_write_3)                           && r == $past(write_3) );
  cover property ( $past(RST_N) && !$past(EN_write_4|EN_write_3) && $past(EN_write_2)                && r == $past(write_2) );
  cover property ( $past(RST_N) && !$past(EN_write_4|EN_write_3|EN_write_2) && $past(EN_write_1)     && r == $past(write_1) );
  cover property ( $past(RST_N) && !$past(EN_write_4|EN_write_3|EN_write_2|EN_write_1) && $past(EN_write_0) && r == $past(write_0) );
  cover property ( $past(RST_N) && !$past(EN_write_4|EN_write_3|EN_write_2|EN_write_1|EN_write_0)    && r == $past(r) );

  // Coverage: simultaneous enables exercise priority
  cover property ( $past(RST_N) && $past(EN_write_4 & EN_write_3)                && r == $past(write_4) );
  cover property ( $past(RST_N) && !$past(EN_write_4) && $past(EN_write_3 & EN_write_2) && r == $past(write_3) );

endmodule