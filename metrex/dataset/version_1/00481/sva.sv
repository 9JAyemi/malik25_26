// SVA for dual_port_memory
// Focus: FSM correctness, control signal legality, data moves, and useful coverage.
module dual_port_memory_sva (dual_port_memory m);

  default clocking cb @(posedge m.clk); endclocking

  bit past_valid;
  always_ff @(posedge m.clk) past_valid <= 1'b1;

  // Basic sanity
  assert property (past_valid |-> m.state inside {m.ACCESO_M1,m.READ_M1,m.WRITE_M1,m.ACCESO_M2,m.READ_M2,m.WRITE_M2});
  assert property (!$isunknown(m.we1_n));
  assert property (!$isunknown(m.we2_n));
  assert property (past_valid |-> !$isunknown(m.dout1));
  assert property (past_valid |-> !$isunknown(m.dout2));

  // FSM transitions (state(t+1) is function of state(t), inputs)
  assert property ((m.state==m.ACCESO_M1 && m.we1_n===1'b1) |=> m.state==m.READ_M1);
  assert property ((m.state==m.ACCESO_M1 && m.we1_n===1'b0) |=> m.state==m.WRITE_M1);
  assert property ((m.state==m.READ_M1)                      |=> m.state==m.ACCESO_M2);
  assert property ((m.state==m.WRITE_M1 && m.we1_n===1'b0)   |=> m.state==m.ACCESO_M2);
  assert property ((m.state==m.WRITE_M1 && m.we1_n===1'b1)   |=> m.state==m.ACCESO_M1);

  assert property ((m.state==m.ACCESO_M2 && m.we2_n===1'b1)  |=> m.state==m.READ_M2);
  assert property ((m.state==m.ACCESO_M2 && m.we2_n===1'b0)  |=> m.state==m.WRITE_M2);
  assert property ((m.state==m.READ_M2)                      |=> m.state==m.ACCESO_M1);
  // WRITE_M2 always returns to ACCESO_M1 per RTL
  assert property (m.state==m.WRITE_M2 |=> m.state==m.ACCESO_M1);

  // Control signal legality
  assert property (m.write_in_dout1 |-> (m.state==m.READ_M1 && m.we1_n===1'b1));
  assert property (m.write_in_dout2 |-> (m.state==m.READ_M2 && m.we2_n===1'b1));
  assert property (!(m.write_in_dout1 && m.write_in_dout2)); // mutually exclusive

  // write_in_dout must assert when the READ conditions are met
  assert property ((m.state==m.READ_M1 && m.we1_n===1'b1) |-> m.write_in_dout1);
  assert property ((m.state==m.READ_M2 && m.we2_n===1'b1) |-> m.write_in_dout2);

  // Data path intent
  // On WRITE states with active write, data_to_write chooses correct source and enable is 1
  assert property ((m.state==m.WRITE_M1 && m.we1_n===1'b0) |-> (m.data_to_write==m.din1 && m.enable_input_to_sram));
  assert property ((m.state==m.WRITE_M2 && m.we2_n===1'b0) |-> (m.data_to_write==m.din2 && m.enable_input_to_sram));

  // Outside WRITE states, data_to_write should be the defined default; enable should be 0
  // (Will flag the current RTL latch on enable_input_to_sram)
  assert property (!(m.state inside {m.WRITE_M1,m.WRITE_M2}) |-> (m.data_to_write==8'h00 && !m.enable_input_to_sram));

  // Output register update semantics
  assert property (m.write_in_dout1 |=> m.dout1 == $past(m.data_to_write));
  assert property (m.write_in_dout2 |=> m.dout2 == $past(m.data_to_write));

  assert property (past_valid && !m.write_in_dout1 |=> $stable(m.dout1));
  assert property (past_valid && !m.write_in_dout2 |=> $stable(m.dout2));

  // DUT output assignment consistency
  assert property (m.dout1 == m.doutput1);
  assert property (m.dout2 == m.doutput2);

  // Coverage: visit all states
  cover property (m.state==m.ACCESO_M1);
  cover property (m.state==m.READ_M1);
  cover property (m.state==m.WRITE_M1);
  cover property (m.state==m.ACCESO_M2);
  cover property (m.state==m.READ_M2);
  cover property (m.state==m.WRITE_M2);

  // Coverage: M1 read path
  cover property ((m.state==m.ACCESO_M1 && m.we1_n==1) ##1 (m.state==m.READ_M1 && m.write_in_dout1));

  // Coverage: M1 write path
  cover property ((m.state==m.ACCESO_M1 && m.we1_n==0) ##1 (m.state==m.WRITE_M1 && m.we1_n==0 && m.data_to_write==m.din1));

  // Coverage: M2 read path
  cover property ((m.state==m.ACCESO_M2 && m.we2_n==1) ##1 (m.state==m.READ_M2 && m.write_in_dout2));

  // Coverage: M2 write path
  cover property ((m.state==m.ACCESO_M2 && m.we2_n==0) ##1 (m.state==m.WRITE_M2 && m.we2_n==0 && m.data_to_write==m.din2));

  // Coverage: round-trip sequence exercising both ports
  cover property (
    (m.state==m.ACCESO_M1 && m.we1_n==0) ##1 (m.state==m.WRITE_M1) ##1
    (m.state==m.ACCESO_M2 && m.we2_n==1) ##1 (m.state==m.READ_M2 && m.write_in_dout2) ##1
    (m.state==m.ACCESO_M1 && m.we1_n==1) ##1 (m.state==m.READ_M1 && m.write_in_dout1)
  );

endmodule

// Bind into all instances of dual_port_memory
bind dual_port_memory dual_port_memory_sva SVA(.m());