// SVA for sky130_fd_sc_hd__fahcon
// Bind these assertions to your DUT

module sky130_fd_sc_hd__fahcon_sva
(
  input logic A,
  input logic B,
  input logic CI,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic COUT_N,
  input logic SUM
);

  function automatic bit is01 (logic s);
    return (s === 1'b0) || (s === 1'b1);
  endfunction

  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === VPWR) && (VNB === VGND);

  // Power pin sanity
  always_comb begin
    if ((VPWR === 1'b1) && (VGND === 1'b0)) begin
      assert (VPB === VPWR && VNB === VGND)
        else $error("Body-bias pins not tied to rails (VPB!=VPWR or VNB!=VGND)");
    end
  end

  // Functional correctness (under good power and known inputs)
  always_comb begin
    if (power_good && is01(A) && is01(B) && is01(CI)) begin
      automatic logic [1:0] exp_sum2;
      exp_sum2 = {1'b0, A} + {1'b0, B} + {1'b0, CI};

      // 2-bit add equivalence: {carry,sum} must equal A+B+CI
      assert ({COUT_N, SUM} === exp_sum2)
        else $error("Adder mismatch: A=%0b B=%0b CI=%0b got {%0b,%0b} exp %0b",
                    A,B,CI,COUT_N,SUM,exp_sum2);

      // Redundant bitwise checks (catch partial mismatches)
      assert (SUM === (A ^ B ^ CI))
        else $error("SUM mismatch: A^B^CI=%0b SUM=%0b", (A^B^CI), SUM);

      assert (COUT_N === ((A & B) | (CI & (A ^ B))))
        else $error("COUT mismatch: (A&B)|(CI&(A^B))=%0b COUT=%0b",
                    ((A&B)|(CI&(A^B))), COUT_N);
    end
  end

  // Deterministic carry in corner cases with unknown CI (X-robustness), under good power
  always_comb begin
    if (power_good) begin
      if (A === 1'b1 && B === 1'b1) begin
        assert (COUT_N === 1'b1) else $error("Carry generate violated when A=B=1");
      end
      if (A === 1'b0 && B === 1'b0) begin
        assert (COUT_N === 1'b0) else $error("Carry kill violated when A=B=0");
      end
    end
  end

  // Coverage: all input combinations under good power
  cover property (power_good && A===1'b0 && B===1'b0 && CI===1'b0);
  cover property (power_good && A===1'b0 && B===1'b0 && CI===1'b1);
  cover property (power_good && A===1'b0 && B===1'b1 && CI===1'b0);
  cover property (power_good && A===1'b0 && B===1'b1 && CI===1'b1);
  cover property (power_good && A===1'b1 && B===1'b0 && CI===1'b0);
  cover property (power_good && A===1'b1 && B===1'b0 && CI===1'b1);
  cover property (power_good && A===1'b1 && B===1'b1 && CI===1'b0);
  cover property (power_good && A===1'b1 && B===1'b1 && CI===1'b1);

  // Coverage: observe all output combinations under good power
  cover property (power_good && {COUT_N,SUM} === 2'b00);
  cover property (power_good && {COUT_N,SUM} === 2'b01);
  cover property (power_good && {COUT_N,SUM} === 2'b10);
  cover property (power_good && {COUT_N,SUM} === 2'b11);

  // Coverage: generate/kill/propagate classes
  cover property (power_good && (A===1'b1) && (B===1'b1)); // generate
  cover property (power_good && (A===1'b0) && (B===1'b0)); // kill
  cover property (power_good && (A!==B));                  // propagate

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__fahcon sky130_fd_sc_hd__fahcon_sva
  sva (.A(A), .B(B), .CI(CI), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .COUT_N(COUT_N), .SUM(SUM));