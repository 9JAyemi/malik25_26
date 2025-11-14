// SVA checker for READ_ROM32. Bind this file to the DUT.
module READ_ROM32_sva;

  // In bind-scope we can see: ADDR, DATA_RE, DATA_IM, re[], im[]

  // Sampling event: on any addr/output change; plus one t=0 sample for $past
  event ev;
  always @(ADDR or DATA_RE or DATA_IM) -> ev;
  initial #0 -> ev;

  default clocking cb @(ev); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(ev) past_valid <= 1'b1;

  // Known ADDR implies outputs are known and equal to ROM contents
  assert property ( (!$isunknown(ADDR))
                    |-> (DATA_RE === re[ADDR]) && (DATA_IM === im[ADDR]) && !$isunknown({DATA_RE,DATA_IM}) );

  // Outputs may only change when ADDR changes
  assert property ( (past_valid && !$isunknown(ADDR) && ($changed(DATA_RE) || $changed(DATA_IM)))
                    |-> $changed(ADDR) );

  // ROM contents are read-only after initialization
  genvar i;
  generate
    for (i=0; i<32; i++) begin : ro_chk
      assert property ( past_valid |-> (re[i] == $past(re[i]) && im[i] == $past(im[i])) );
    end
  endgenerate

  // Functional coverage: hit every address and see correct data on both outputs
  genvar j;
  generate
    for (j=0; j<32; j++) begin : addr_cov
      cover property ( ADDR == j && DATA_RE === re[j] && DATA_IM === im[j] );
    end
  endgenerate

endmodule

bind READ_ROM32 READ_ROM32_sva rom32_sva();