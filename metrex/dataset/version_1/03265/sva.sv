// Bind these assertions into the DUT
bind xnor_gate xnor_gate_sva sva_inst();

module xnor_gate_sva;
  // Access DUT scope directly via bind
  wire pwr_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Combinational checks under valid power
  always @* begin
    if (pwr_good) begin
      // Inputs/controls known
      assert (!$isunknown({A,B,input_state})) else $error("xnor_gate: X/Z on inputs/controls");

      // Internal correctness
      assert (xnor_out[0] == xnor_out[1]) else $error("xnor_gate: xnor_out bits mismatch");
      assert (xnor_out[0] == (A ^ B)) else $error("xnor_gate: xnor_out != A^B");

      // Output selection correctness (matches RTL)
      unique case (input_state)
        2'b00: assert (Y == xnor_out[0]) else $error("xnor_gate: sel00 mismatch");
        2'b01: assert (Y == xnor_out[1]) else $error("xnor_gate: sel01 mismatch");
        2'b10: assert (Y == (xnor_out[0] & xnor_out[1])) else $error("xnor_gate: sel10 mismatch");
        2'b11: assert (Y == (~xnor_out[0] & ~xnor_out[1])) else $error("xnor_gate: sel11 mismatch");
      endcase

      // Output known when inputs known
      assert (!$isunknown(Y)) else $error("xnor_gate: Y is X/Z under pwr_good");

      // Unused state should not change
      assert ($stable(state)) else $error("xnor_gate: state changed unexpectedly");
    end
  end

  // Functional coverage under valid power
  always @* begin
    if (pwr_good) begin
      // All selector values seen
      cover (input_state == 2'b00);
      cover (input_state == 2'b01);
      cover (input_state == 2'b10);
      cover (input_state == 2'b11);

      // XOR mode (input_state != 11)
      cover (input_state != 2'b11 && A==0 && B==0 && Y==0);
      cover (input_state != 2'b11 && A==0 && B==1 && Y==1);
      cover (input_state != 2'b11 && A==1 && B==0 && Y==1);
      cover (input_state != 2'b11 && A==1 && B==1 && Y==0);

      // XNOR mode (input_state == 11)
      cover (input_state == 2'b11 && A==0 && B==0 && Y==1);
      cover (input_state == 2'b11 && A==0 && B==1 && Y==0);
      cover (input_state == 2'b11 && A==1 && B==0 && Y==0);
      cover (input_state == 2'b11 && A==1 && B==1 && Y==1);
    end
  end
endmodule