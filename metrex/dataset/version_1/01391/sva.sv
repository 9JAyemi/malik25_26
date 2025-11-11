// SVA for top_module
// Bind this file to the DUT: bind top_module top_module_sva sva();

module top_module_sva (top_module m);
  default clocking @(posedge $global_clock); endclocking

  // Illegal: divide-by-zero to divider
  assert property (m.V != 16'd0)
    else $error("div_16bit_unsigned: V must not be zero");

  // Comparator correctness on low nibble
  assert property (1'b1 |-> ##0 (m.equal  == (m.D[3:0] == m.V[3:0])));
  assert property (1'b1 |-> ##0 (m.greater== (m.D[3:0] >  m.V[3:0])));
  assert property (1'b1 |-> ##0 !(m.equal && m.greater));

  // Divider algebra and remainder range (only when legal)
  assert property ((m.V!=16'd0) |-> ##0 (m.D == (m.div_inst.Q * m.V + m.div_inst.R)));
  assert property ((m.V!=16'd0) |-> ##0 (m.div_inst.R < m.V));

  // Functional module output selection
  assert property (1'b1 |-> ##0 (m.Q_out == (m.greater ? m.div_inst.Q[15:12]
                                                       : m.div_inst.Q[3:0])));

  // Knownness when inputs are known and division is legal
  assert property ((!( $isunknown({m.D,m.V}) ) && m.V!=16'd0)
                    |-> ##0 !( $isunknown({m.equal,m.greater,m.div_inst.Q,m.div_inst.R,m.Q_out}) ));

  // Meaningful coverage
  cover property (m.D[3:0] == m.V[3:0]);         // equal case
  cover property (m.D[3:0] >  m.V[3:0]);         // greater case
  cover property (m.D[3:0] <  m.V[3:0]);         // less-than case
  cover property ((m.V!=16'd0) && (m.div_inst.R==16'd0)); // exact division
  cover property ((m.V!=16'd0) && (m.D < m.V));  // Q==0 scenario
  cover property ( m.greater && (m.Q_out == m.div_inst.Q[15:12]) );
  cover property (!m.greater && (m.Q_out == m.div_inst.Q[3:0]) );
  cover property (m.V==16'd0);                   // observe illegal stimulus if it occurs
endmodule