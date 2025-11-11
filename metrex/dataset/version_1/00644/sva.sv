// SVA for fp_convert_altpriority_encoder_3v7 / 3e8 / 6v7
// Bind these into the DUTs.

module fp_convert_altpriority_encoder_3v7_sva (
  input  [2:0] data,
  input  [1:0] q
);
  // Functional correctness (simplified form of RTL): q = {~|data, ~|data[2:1]}
  always_comb begin
    assert (q[1] === ~(|data))          else $error("3v7: q[1] != ~|data");
    assert (q[0] === ~(|data[2:1]))     else $error("3v7: q[0] != ~|data[2:1]");
    if (!$isunknown(data)) assert (!$isunknown(q)) else $error("3v7: X/Z on q with known data");
  end

  // Compact functional coverage
  cover (data == 3'b000 && q == 2'b11); // all zero
  cover (data[2:1] == 2'b00 && data[0] && q == 2'b01); // upper two zero, LSB 1
  cover (data[2:1] != 2'b00 && q == 2'b00); // upper two not both zero
endmodule

bind fp_convert_altpriority_encoder_3v7
  fp_convert_altpriority_encoder_3v7_sva (.data(data), .q(q));



module fp_convert_altpriority_encoder_3e8_sva (
  input  [2:0] data,
  input  [1:0] q,
  input        zero,
  input  [1:0] q0, q1, q2, q3
);
  // From instantiated 3v7s: qx[1] must all equal ~|data
  // DUT function reduces to q = {Z, Z} and zero = Z, where Z = ~|data
  always_comb begin
    assert (zero === ~(|data))          else $error("3e8: zero != ~|data");
    assert (q[1] === ~(|data))          else $error("3e8: q[1] != ~|data");
    assert (q[0] === ~(|data))          else $error("3e8: q[0] != ~|data");
    assert (q0[1] === ~(|data))         else $error("3e8: q0[1] != ~|data");
    assert (q1[1] === ~(|data))         else $error("3e8: q1[1] != ~|data");
    assert (q2[1] === ~(|data))         else $error("3e8: q2[1] != ~|data");
    assert (q3[1] === ~(|data))         else $error("3e8: q3[1] != ~|data");
    if (!$isunknown(data)) assert (!$isunknown({q,zero})) else $error("3e8: X/Z on outputs with known data");
  end

  // Coverage
  cover (data == 3'b000 && zero && q == 2'b11);
  cover (data != 3'b000 && !zero && q == 2'b00);
endmodule

bind fp_convert_altpriority_encoder_3e8
  fp_convert_altpriority_encoder_3e8_sva (.data(data), .q(q), .zero(zero), .q0(q0), .q1(q1), .q2(q2), .q3(q3));



module fp_convert_altpriority_encoder_6v7_sva (
  input  [3:0] data,
  input  [2:0] q,
  input  [1:0] wire_altpriority_encoder21_q,
  input  [1:0] wire_altpriority_encoder22_q
);
  // Derived behavior (given the current RTL):
  // - wire_altpriority_encoder22_q[1:0] == {Z31, Z31}, Z31 = ~|data[3:1]
  // - wire_altpriority_encoder21_q[1]   == Z210       , Z210 = ~|{data[2:1],data[0]} == ~|data[2:0]
  // - q[2] == 1'b0 (width mismatch in RTL yields zero-extend)
  // - q[1] == |data[3:1]  (i.e., ~Z31)
  // - q[0] == ~|data[3:0]
  logic Z31, Z210;
  assign Z31  = ~(|data[3:1]);
  assign Z210 = ~(|{data[2:1], data[0]});

  always_comb begin
    assert (wire_altpriority_encoder22_q[1] === Z31) else $error("6v7: enc22_q[1] != ~|data[3:1]");
    assert (wire_altpriority_encoder22_q[0] === Z31) else $error("6v7: enc22_q[0] != ~|data[3:1]");
    assert (wire_altpriority_encoder21_q[1] === Z210) else $error("6v7: enc21_q[1] != ~|{data[2:1],data[0]}");

    assert (q[2] === 1'b0)              else $error("6v7: q[2] expected 0 (zero-extend)");
    assert (q[1] === (|data[3:1]))      else $error("6v7: q[1] != |data[3:1]");
    assert (q[0] === ~(|data))          else $error("6v7: q[0] != ~|data[3:0]");

    if (!$isunknown(data)) assert (!$isunknown(q)) else $error("6v7: X/Z on q with known data");
  end

  // Coverage
  cover (data == 4'b0000 && q == 3'b001);
  cover (data == 4'b0001 && q == 3'b000);
  cover (|data[3:1] && !data[0] && q == 3'b010);
endmodule

bind fp_convert_altpriority_encoder_6v7
  fp_convert_altpriority_encoder_6v7_sva (.data(data), .q(q),
    .wire_altpriority_encoder21_q(wire_altpriority_encoder21_q),
    .wire_altpriority_encoder22_q(wire_altpriority_encoder22_q));