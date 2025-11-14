// SVA for sky130_fd_sc_hd__dlrtn_4 (1-bit retained register with gate)
module sky130_fd_sc_hd__dlrtn_4_sva (sky130_fd_sc_hd__dlrtn_4 m);

  default clocking cb @(posedge m.RESET_B); endclocking

  // Sanity: inputs known at capture edge, output known after update
  assert property ( !$isunknown({m.GATE_N, m.D}) );
  assert property ( !$isunknown(m.Q) );

  // D_ff captures D on every posedge RESET_B
  assert property ( m.D_ff == $past(m.D) );

  // Q_int update behavior (gate or hold)
  assert property (  m.GATE_N  |-> m.Q_int == $past(m.D_ff) );
  assert property ( !m.GATE_N  |-> m.Q_int == $past(m.Q_int) );

  // Output mirrors internal state
  assert property ( m.Q == m.Q_int );

  // Equivalent end-to-end: when gated, Q reflects prior-cycle D
  assert property ( m.GATE_N |-> m.Q == $past(m.D) );

  // Coverage
  cover property (  m.GATE_N  );                  // gate pass case seen
  cover property ( !m.GATE_N  );                  // gate hold case seen
  cover property (  m.GATE_N && $changed(m.Q_int) ); // Q_int updates
  cover property ( !m.GATE_N && $stable (m.Q_int) ); // Q_int holds
  cover property (  m.GATE_N && (m.Q == $past(m.D)) ); // end-to-end update

endmodule

bind sky130_fd_sc_hd__dlrtn_4 sky130_fd_sc_hd__dlrtn_4_sva svai (.*);


// SVA for sky130_fd_sc_hd__dlrtn (4-bit retained register, Q = LSB)
module sky130_fd_sc_hd__dlrtn_sva (sky130_fd_sc_hd__dlrtn m);

  default clocking cb @(posedge m.RESET_B); endclocking

  // Sanity: inputs known at capture edge, output known after update
  assert property ( !$isunknown({m.GATE_N, m.D}) );
  assert property ( !$isunknown(m.Q) );

  // D_ff captures D on every posedge RESET_B
  assert property ( m.D_ff == $past(m.D) );

  // Q_int update behavior (vector gate or hold)
  assert property (  m.GATE_N  |-> m.Q_int == $past(m.D_ff) );
  assert property ( !m.GATE_N  |-> m.Q_int == $past(m.Q_int) );

  // Output is LSB of internal vector
  assert property ( m.Q == m.Q_int[0] );

  // End-to-end (LSB): when gated, Q reflects prior-cycle D[0]
  assert property ( m.GATE_N |-> m.Q == $past(m.D[0]) );

  // Coverage
  cover property (  m.GATE_N  );
  cover property ( !m.GATE_N  );
  cover property (  m.GATE_N && (m.Q_int != $past(m.Q_int)) ); // some bit updated
  cover property ( !m.GATE_N && $stable(m.Q_int) );
  cover property (  m.GATE_N && (m.Q == $past(m.D[0])) );

endmodule

bind sky130_fd_sc_hd__dlrtn sky130_fd_sc_hd__dlrtn_sva svai (.*);