// addsub SVA (bindable). Focused, concise, and checks both functional and internal equivalence.

`ifndef ADDSUB_SVA_SV
`define ADDSUB_SVA_SV

// Port-only functional checks (no reliance on internals)
module addsub_sva_ports;

  // Functional equivalence: when inputs are known, outputs match golden model
  always_comb begin
    if (!$isunknown({A,B,C})) begin
      automatic logic [4:0] exp;
      exp = {1'b0, A} + {1'b0, (C ? ((~B) + 4'd1) : B)};
      assert ({Cout, S} == exp)
        else $error("addsub mismatch A=%0h B=%0h C=%0b exp=%0h got=%0b_%0h", A, B, C, exp, Cout, S);
      assert (!$isunknown({S,Cout}))
        else $error("addsub X/Z on outputs with known inputs A=%0h B=%0h C=%0b", A, B, C);
    end
  end

  // Key scenario coverage
  always_comb begin
    cover (! $isunknown({A,B,C}) && C==0);                            // add mode
    cover (! $isunknown({A,B,C}) && C==1);                            // sub mode
    cover (! $isunknown({A,B,C}) && C==0 && Cout==1);                 // carry on add
    cover (! $isunknown({A,B,C}) && C==1 && Cout==0);                 // borrow on sub
    cover (! $isunknown({A,B,C}) && C==1 && A==B && S==0 && Cout==1); // A-B==0
    cover (! $isunknown({A,B,C}) && S==4'h0);                         // zero result
  end

endmodule

// Internal-structure checks (relies on DUT internals; bind only if available)
module addsub_sva_internals;

  always_comb begin
    if (!$isunknown(B)) begin
      assert (B_neg == ((~B) + 4'd1))
        else $error("B_neg wrong B=%0h B_neg=%0h", B, B_neg);
    end
    if (!$isunknown({B_neg,B,C})) begin
      assert (B_sel == (C ? B_neg : B))
        else $error("B_sel wrong C=%0b B=%0h B_neg=%0h B_sel=%0h", C, B, B_neg, B_sel);
    end
    if (!$isunknown({A,B_sel})) begin
      assert ({C_add,S_add} == ({1'b0,A} + {1'b0,B_sel}))
        else $error("Adder wrong A=%0h B_sel=%0h sum=%0h_%0h", A, B_sel, C_add, S_add);
    end
    if (!$isunknown({S_add,C_add})) begin
      assert (S == S_add) else $error("S not from S_add");
      assert (Cout == C_add) else $error("Cout not from C_add");
    end
  end

  // Ensure mux uses both arms
  always_comb begin
    cover (! $isunknown({B,C}) && C==0 && B_sel==B);
    cover (! $isunknown({B,C}) && C==1 && B_sel==B_neg);
  end

endmodule

// Bind into all addsub instances
bind addsub addsub_sva_ports      u_addsub_sva_ports();
bind addsub addsub_sva_internals  u_addsub_sva_internals();

`endif