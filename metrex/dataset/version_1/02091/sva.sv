// SVA checker for multiplicadorPuntoFijo
// Bind-only, no clock required (purely combinational DUT)
// Focused, high-quality assertions with essential coverage

module mul_fixed_chk #(parameter int Width=24, Magnitud=4, Precision=19, Signo=1) ();

  localparam int W  = Width;
  localparam int M  = Magnitud;
  localparam int P  = Precision;
  localparam int S  = Signo;
  localparam int HI = 2*W - 1 - M - S;

  // Robust saturation constants
  localparam logic signed [W-1:0] MAX_POS = {1'b0, {(W-1){1'b1}}};
  localparam logic signed [W-1:0] MIN_NEG = {1'b1, {(W-1){1'b0}}};

  // Parameter sanity
  initial begin
    assert (W > 0 && M >= 0 && P >= 0 && S >= 0) else $error("Bad params: Width/Magnitud/Precision/Signo must be non-negative");
    assert (M + P + S == W) else $error("Bad params: Magnitud + Precision + Signo must equal Width");
    assert (HI >= P) else $error("Bad params: slice [%0d:%0d] invalid", HI, P);
  end

  // Short local names (hierarchical from bind scope)
  // inputs:  EnableMul, In, Coeff
  // outputs: OutMul, Error
  // internals: AuxMul, Overflow, Underflow

  // No-X on outputs when inputs are known
  always_comb
    if (!$isunknown({EnableMul, In, Coeff}))
      assert #0 (!$isunknown({AuxMul, Overflow, Underflow, OutMul, Error}))
        else $error("Outputs/internal contain X/Z with known inputs");

  // AuxMul gating and multiply
  always_comb
    assert #0 (EnableMul ? (AuxMul == $signed(In) * $signed(Coeff))
                         : (AuxMul == '0))
      else $error("AuxMul wrong: Enable=%0b In=%0d Coeff=%0d AuxMul=%0d", EnableMul, In, Coeff, AuxMul);

  // Overflow / Underflow logic correctness
  wire sign_in    = In[W-1];
  wire sign_coef  = Coeff[W-1];
  wire guard_bit  = AuxMul[HI];

  always_comb begin
    logic exp_ovf = ((~sign_in && ~sign_coef && guard_bit) ||
                     ( sign_in &&  sign_coef && guard_bit));
    logic exp_udf = ((~sign_in &&  sign_coef && ~guard_bit) ||
                     ( sign_in && ~sign_coef && ~guard_bit));

    assert #0 (Overflow  == exp_ovf) else $error("Overflow mismatch");
    assert #0 (Underflow == exp_udf) else $error("Underflow mismatch");
    assert #0 (!(Overflow && Underflow)) else $error("Overflow and Underflow both 1");
  end

  // Error mapping
  always_comb
    assert #0 (Error == (Overflow || Underflow))
      else $error("Error != Overflow|Underflow");

  // OutMul selection
  always_comb begin
    if ((In == '0) || (Coeff == '0)) begin
      assert #0 (OutMul == '0) else $error("OutMul must be 0 when any operand is 0");
    end
    else if (Overflow) begin
      assert #0 (OutMul == MAX_POS) else $error("OutMul must saturate to MAX_POS on Overflow");
    end
    else if (Underflow) begin
      assert #0 (OutMul == MIN_NEG) else $error("OutMul must saturate to MIN_NEG on Underflow");
    end
    else begin
      assert #0 (OutMul == AuxMul[HI:P]) else $error("OutMul slice mismatch");
    end
  end

  // Lightweight coverage
  always_comb begin
    cover (EnableMul);
    cover (!EnableMul);

    cover ((In == '0) || (Coeff == '0));                            // zero case
    cover ((In != '0) && (Coeff != '0) && !Overflow && !Underflow); // normal case

    cover (Overflow);
    cover (Underflow);
    cover (OutMul == MAX_POS);
    cover (OutMul == MIN_NEG);

    // Sign/guard combinations driving status
    cover ((~sign_in && ~sign_coef && guard_bit));   // +,+ with guard=1 -> Overflow
    cover (( sign_in &&  sign_coef && guard_bit));   // -,- with guard=1 -> Overflow
    cover ((~sign_in &&  sign_coef && ~guard_bit));  // +,- with guard=0 -> Underflow
    cover (( sign_in && ~sign_coef && ~guard_bit));  // -,+ with guard=0 -> Underflow

    // Guard bit toggling
    cover (AuxMul[HI] == 1'b0);
    cover (AuxMul[HI] == 1'b1);
  end

endmodule

// Bind the checker to the DUT (parameters propagate)
bind multiplicadorPuntoFijo
  mul_fixed_chk #(.Width(Width), .Magnitud(Magnitud), .Precision(Precision), .Signo(Signo)) u_mul_fixed_chk();