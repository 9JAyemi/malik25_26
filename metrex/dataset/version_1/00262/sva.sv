// SVA for DSP_PREADD (bindable, concise, high-quality checks and coverage)
module DSP_PREADD_sva #(parameter W=27)
(
  input  logic               ADDSUB,
  input  logic               INMODE2,
  input  logic [W-1:0]       D_DATA,
  input  logic [W-1:0]       PREADD_AB,
  input  logic [W-1:0]       AD
);

  // Sample on any relevant signal change (combinational DUT)
  event ev_change;
  always @(ADDSUB or INMODE2 or D_DATA or PREADD_AB or AD) -> ev_change;
  default clocking cb @(ev_change); endclocking

  // Helpful lets
  let D_GATE = INMODE2 ? D_DATA : {W{1'b0}};
  let SUM    = D_GATE + PREADD_AB;
  let DIFF   = D_GATE - PREADD_AB;

  // Core functional equivalence (when inputs are known)
  property p_func_eq;
    !($isunknown({ADDSUB, INMODE2, D_DATA, PREADD_AB})) |->
      AD == (ADDSUB ? DIFF : SUM);
  endproperty
  assert property (p_func_eq);

  // Output must be known when controlling/selected inputs are known
  property p_known_out_if_known_in;
    !($isunknown({ADDSUB, INMODE2, PREADD_AB})) && (INMODE2 || !($isunknown(D_DATA)))
      |->
    !($isunknown(AD));
  endproperty
  assert property (p_known_out_if_known_in);

  // Masking behavior: when INMODE2==0, D path is forced to zero
  property p_masking_correct;
    !($isunknown({ADDSUB, INMODE2, PREADD_AB})) && (INMODE2==1'b0)
      |->
    AD == (ADDSUB ? ({W{1'b0}} - PREADD_AB) : (PREADD_AB));
  endproperty
  assert property (p_masking_correct);

  // Mode-specific checks (redundant to p_func_eq, but clearer failures)
  assert property ( !($isunknown({INMODE2, D_DATA, PREADD_AB})) && (ADDSUB==1'b0) |->
                    AD == SUM );
  assert property ( !($isunknown({INMODE2, D_DATA, PREADD_AB})) && (ADDSUB==1'b1) |->
                    AD == DIFF );

  // Basic mode/gating coverage
  cover property (ADDSUB==0 && INMODE2==0);
  cover property (ADDSUB==0 && INMODE2==1);
  cover property (ADDSUB==1 && INMODE2==0);
  cover property (ADDSUB==1 && INMODE2==1);

  // Corner value coverage
  cover property (INMODE2==1 && D_DATA=='0 && PREADD_AB=='0);
  cover property (INMODE2==1 && D_DATA=={W{1'b1}});
  cover property (PREADD_AB=={W{1'b1}});

  // Wrap-around/underflow coverage
  cover property ( (ADDSUB==0) && (SUM[W-1:0] < D_GATE) );       // addition overflow (wrap)
  cover property ( (ADDSUB==1) && (D_GATE < PREADD_AB) );        // subtraction underflow (wrap)

endmodule

// Bind into the DUT
bind DSP_PREADD DSP_PREADD_sva #(.W(27)) u_DSP_PREADD_sva (.*);