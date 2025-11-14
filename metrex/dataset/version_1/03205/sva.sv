// SVA checker for nand_gate. Bind this to the DUT.
module nand_gate_sva (input logic A, B, Z);

  // Functional equivalence (4-state aware) and no-X on Z when inputs are known
  always_comb begin
    assert (Z === ~(A & B)) else $error("NAND mismatch: Z=%b A=%b B=%b", Z, A, B);
    if ((A !== 1'bx) && (B !== 1'bx)) begin
      assert (Z !== 1'bx && Z !== 1'bz)
        else $error("Z unknown while inputs known: Z=%b A=%b B=%b", Z, A, B);
    end
  end

  // Zero-latency response to input changes (evaluate after delta)
  property p_zero_latency;
    @(posedge A or negedge A or posedge B or negedge B)
      ##0 (Z === ~(A & B));
  endproperty
  assert property (p_zero_latency);

  // Truth-table coverage (2-state)
  cover property (@(posedge A or negedge A or posedge B or negedge B)
                  (A===1'b0 && B===1'b0 && Z===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B)
                  (A===1'b0 && B===1'b1 && Z===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B)
                  (A===1'b1 && B===1'b0 && Z===1'b1));
  cover property (@(posedge A or negedge A or posedge B or negedge B)
                  (A===1'b1 && B===1'b1 && Z===1'b0));

  // Z toggle coverage
  cover property (@(posedge Z) 1'b1);
  cover property (@(negedge Z) 1'b1);

endmodule

// Bind to DUT
bind nand_gate nand_gate_sva u_nand_gate_sva (.A(A), .B(B), .Z(Z));