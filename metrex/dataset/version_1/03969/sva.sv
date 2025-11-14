// SVA for four_bit_adder
// Bind this checker to the DUT
bind four_bit_adder four_bit_adder_sva dut_sva();

module four_bit_adder_sva();

  // Combinational sampling event (fires on any comb change)
  event comb_ev;
  always @* -> comb_ev;

  // Suppress checks when inputs are X/Z
  default disable iff ($isunknown({A,B,Cin}));

  // Sanity: outputs must be known when inputs are known
  assert property (@(comb_ev) !$isunknown({Sum,Cout,temp_sum,temp_carry}));

  // Top-level arithmetic correctness (width-safe)
  assert property (@(comb_ev) {Cout,Sum} == ({1'b0,A} + {1'b0,B} + {4'b0,Cin}));

  // Structural consistency
  assert property (@(comb_ev) Sum == temp_sum);

  // Bitwise full-adder equations and carry ripple
  genvar i;
  for (i=0; i<4; i++) begin : bit_checks
    if (i==0) begin
      assert property (@(comb_ev) Sum[0] == (A[0]^B[0]^Cin));
      assert property (@(comb_ev) temp_carry[0] == ((A[0]&B[0]) | (Cin & (A[0]^B[0]))));
      // coverage: generate/propagate/kill at bit0
      cover property (@(comb_ev) (A[0]&B[0]) &&  temp_carry[0]);                 // generate
      cover property (@(comb_ev)  Cin && (A[0]^B[0]) &&  temp_carry[0]);         // propagate
      cover property (@(comb_ev)  Cin && ~A[0] && ~B[0] && !temp_carry[0]);      // kill
    end
    else if (i<3) begin
      assert property (@(comb_ev) Sum[i] == (A[i]^B[i]^temp_carry[i-1]));
      assert property (@(comb_ev) temp_carry[i] == ((A[i]&B[i]) | (temp_carry[i-1] & (A[i]^B[i]))));
      // coverage: generate/propagate/kill at bit1..2
      cover property (@(comb_ev) (A[i]&B[i]) &&  temp_carry[i]);                 // generate
      cover property (@(comb_ev)  temp_carry[i-1] && (A[i]^B[i]) &&  temp_carry[i]); // propagate
      cover property (@(comb_ev)  temp_carry[i-1] && ~A[i] && ~B[i] && !temp_carry[i]); // kill
    end
    else begin // i==3 (MSB)
      assert property (@(comb_ev) Sum[3] == (A[3]^B[3]^temp_carry[2]));
      assert property (@(comb_ev) Cout   == ((A[3]&B[3]) | (temp_carry[2] & (A[3]^B[3]))));
      // coverage: generate/propagate/kill at MSB
      cover property (@(comb_ev) (A[3]&B[3]) &&  Cout);                          // generate
      cover property (@(comb_ev)  temp_carry[2] && (A[3]^B[3]) &&  Cout);        // propagate
      cover property (@(comb_ev)  temp_carry[2] && ~A[3] && ~B[3] && !Cout);     // kill
    end
  end

  // Global covers
  cover property (@(comb_ev) !Cout);                         // no overflow
  cover property (@(comb_ev)  Cout);                         // overflow
  cover property (@(comb_ev) (A==4'h0 && B==4'h0 && !Cin));  // min case
  cover property (@(comb_ev) (A==4'hF && B==4'hF &&  Cin));  // max case with carry
  // Full 4-bit propagate chain (Cin ripples through all bits)
  cover property (@(comb_ev) (Cin && ((A^B)==4'hF) && ((A&B)==4'h0) && Cout && (Sum==4'h0)));

endmodule