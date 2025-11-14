// SVA for divider
// Bind into DUT: bind divider divider_sva i_divider_sva();

module divider_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset values
  assert property (rst |=> state==2'd0 && ready_o==1'b0 && result_o==64'd0);

  // Idle behavior
  assert property (state==2'd0 && !start_i |=> state==2'd0);

  // Start (non-zero divisor) initialization
  assert property (state==2'd0 && start_i && (opdata2_i!=32'd0)
                   |=> state==2'd1 && counter==6'd0
                       && dividend==opdata1_i && divisor==opdata2_i && quotient==64'd0);

  // Start with divisor==0 path: 2-cycle response with ready and zero result, then back to idle
  assert property (state==2'd0 && start_i && (opdata2_i==32'd0)
                   |=> state==2'd3 ##1 (ready_o && result_o==64'd0 && state==2'd0));

  // Annul during division returns to idle and does not assert ready
  assert property (state==2'd1 && annul_i |=> state==2'd0 && !ready_o);

  // Counter progression during active division
  assert property (state==2'd1 && !annul_i && counter!=6'd32
                   |=> counter == $past(counter)+6'd1);

  // Dividend and quotient shift behavior during division
  assert property (state==2'd1 && !annul_i && counter!=6'd32
                   |=> dividend == {$past(dividend)[30:0],1'b0}
                       && quotient[63:1] == $past(quotient)[62:0]
                       && quotient[0] == $past(dividend[31]));

  // Enter end state when counter hits 32
  assert property (state==2'd1 && !annul_i && counter==6'd32 |=> state==2'd2);

  // End state: ready asserted, result equals previous quotient; next state is idle
  assert property (state==2'd2 |-> ready_o && result_o == $past(quotient));
  assert property (state==2'd2 |=> state==2'd0);

  // Ready should only be asserted in end/err states (flags sticky ready bug if violated)
  assert property (ready_o |-> (state==2'd2 || state==2'd3));

  // No ready while actively dividing (flags sticky ready bug if violated)
  assert property (state==2'd1 |-> !ready_o);

  // Divisor must remain stable during division
  assert property (state==2'd1 && !annul_i && counter!=6'd32 |-> divisor == $past(divisor));

  // Implementation: quotient is sign-corrected one cycle after state2 when needed
  assert property (state==2'd2 && signed_div_i && (opdata1_i[31]^opdata2_i[31])
                   |=> quotient == (~$past(quotient))+64'd1);

  // Intent/spec check: result should be sign-corrected in signed mixed-sign case (will fail on current RTL)
  assert property (state==2'd2 && signed_div_i && (opdata1_i[31]^opdata2_i[31])
                   |-> result_o == ((~$past(quotient))+64'd1));

  // Coverage
  cover property (state==2'd0 && start_i && (opdata2_i!=32'd0) ##34 ready_o);
  cover property (state==2'd0 && start_i && (opdata2_i==32'd0) ##2 ready_o);
  cover property (state==2'd0 && start_i && (opdata2_i!=32'd0)
                  ##[1:10] (state==2'd1 && annul_i) ##1 state==2'd0);
  cover property (state==2'd2 && signed_div_i && (opdata1_i[31]^opdata2_i[31]));

endmodule