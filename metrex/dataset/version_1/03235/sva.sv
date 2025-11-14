// SVA checker for var18_multi
module var18_multi_sva #(parameter bit USE_CLK = 0) (
  input  logic clk, // tie to TB clock if USE_CLK=1, else can tie 1'b0
  input  logic A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R,
  input  logic valid
);
  // Constants (match DUT)
  localparam logic [8:0] MIN_VALUE  = 9'd120;
  localparam logic [8:0] MAX_WEIGHT = 9'd60;
  localparam logic [8:0] MAX_VOLUME = 9'd60;

  // Recompute totals (match DUT math and widths)
  logic [8:0] total_value_exp;
  logic [8:0] total_weight_exp;
  logic [8:0] total_volume_exp;

  assign total_value_exp =
        A * 9'd4
      + B * 9'd8
      + C * 9'd0
      + D * 9'd20
      + E * 9'd10
      + F * 9'd12
      + G * 9'd18
      + H * 9'd14
      + I * 9'd6
      + J * 9'd15
      + K * 9'd30
      + L * 9'd8
      + M * 9'd16
      + N * 9'd18
      + O * 9'd18
      + P * 9'd14
      + Q * 9'd7
      + R * 9'd7;

  assign total_weight_exp =
        A * 9'd28
      + B * 9'd8
      + C * 9'd27
      + D * 9'd18
      + E * 9'd27
      + F * 9'd28
      + G * 9'd6
      + H * 9'd1
      + I * 9'd20
      + J * 9'd0
      + K * 9'd5
      + L * 9'd13
      + M * 9'd8
      + N * 9'd14
      + O * 9'd22
      + P * 9'd12
      + Q * 9'd23
      + R * 9'd26;

  assign total_volume_exp =
        A * 9'd27
      + B * 9'd27
      + C * 9'd4
      + D * 9'd4
      + E * 9'd0
      + F * 9'd24
      + G * 9'd4
      + H * 9'd20
      + I * 9'd12
      + J * 9'd15
      + K * 9'd5
      + L * 9'd2
      + M * 9'd9
      + N * 9'd28
      + O * 9'd19
      + P * 9'd18
      + Q * 9'd30
      + R * 9'd12;

  logic expected_valid;
  assign expected_valid =
      (total_value_exp >= MIN_VALUE)
   && (total_weight_exp <= MAX_WEIGHT)
   && (total_volume_exp <= MAX_VOLUME);

  // Combinational correctness and sanity checks
  always_comb begin
    // No X/Z on inputs/outputs
    assert (!$isunknown({A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,valid}))
      else $error("var18_multi: X/Z detected on inputs/valid");

    // Functional equivalence
    assert (valid === expected_valid)
      else $error("var18_multi: valid mismatch. exp=%0b got=%0b", expected_valid, valid);

    // Range protection (guards against unintended truncation changes)
    assert (total_value_exp  <= 9'd225) else $error("total_value overflow");
    assert (total_weight_exp <= 9'd286) else $error("total_weight overflow");
    assert (total_volume_exp <= 9'd260) else $error("total_volume overflow");
  end

  // Optional clocked assertions/coverage
  if (USE_CLK) begin : clked
    // Past-valid to guard $past() usage
    logic past_ok;
    initial past_ok = 1'b0;
    always_ff @(posedge clk) past_ok <= 1'b1;

    default clocking cb @(posedge clk); endclocking
    default disable iff (!past_ok);

    // Clocked equivalence (samples on clk)
    assert property (valid == expected_valid);

    // Unknown-free each cycle
    assert property (!$isunknown({A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,valid}));

    // Boundary coverage
    cover property (valid);
    cover property (total_value_exp  == MIN_VALUE  && total_weight_exp <= MAX_WEIGHT && total_volume_exp <= MAX_VOLUME);
    cover property (total_weight_exp == MAX_WEIGHT && total_value_exp  >= MIN_VALUE  && total_volume_exp <= MAX_VOLUME);
    cover property (total_volume_exp == MAX_VOLUME && total_value_exp  >= MIN_VALUE  && total_weight_exp <= MAX_WEIGHT);
    cover property (total_value_exp  == MIN_VALUE  && total_weight_exp == MAX_WEIGHT && total_volume_exp == MAX_VOLUME);

    // Off-by-one (invalid just outside limits)
    cover property (total_value_exp  == (MIN_VALUE-1) && total_weight_exp <= MAX_WEIGHT && total_volume_exp <= MAX_VOLUME && !valid);
    cover property (total_weight_exp == (MAX_WEIGHT+1) && total_value_exp  >= MIN_VALUE && total_volume_exp <= MAX_VOLUME && !valid);
    cover property (total_volume_exp == (MAX_VOLUME+1) && total_value_exp  >= MIN_VALUE && total_weight_exp <= MAX_WEIGHT && !valid);

    // Pack inputs for concise delta checks and toggle coverage
    logic [17:0] invec;
    always_comb invec = {R,Q,P,O,N,M,L,K,J,I,H,G,F,E,D,C,B,A}; // invec[0]=A, ... invec[17]=R

    // Coefficients (A..R order)
    localparam int unsigned VAL_COEF [18] = '{4,8,0,20,10,12,18,14,6,15,30,8,16,18,18,14,7,7};
    localparam int unsigned WGT_COEF [18] = '{28,8,27,18,27,28,6,1,20,0,5,13,8,14,22,12,23,26};
    localparam int unsigned VOL_COEF [18] = '{27,27,4,4,0,24,4,20,12,15,5,2,9,28,19,18,30,12};

    int v_int, w_int, vol_int;
    always_comb begin
      v_int   = total_value_exp;
      w_int   = total_weight_exp;
      vol_int = total_volume_exp;
    end

    genvar i;
    for (i = 0; i < 18; i++) begin : per_bit
      // Toggle coverage for each input
      cover property ($rose(invec[i]));
      cover property ($fell(invec[i]));

      // Single-bit toggle delta checks (only one bit changed)
      assert property ( ((invec ^ $past(invec)) == (18'b1 << i)) && $rose(invec[i])
                        |-> ( (v_int   - $past(v_int))   == VAL_COEF[i]
                           && (w_int   - $past(w_int))   == WGT_COEF[i]
                           && (vol_int - $past(vol_int)) == VOL_COEF[i] ) );

      assert property ( ((invec ^ $past(invec)) == (18'b1 << i)) && $fell(invec[i])
                        |-> ( ($past(v_int)   - v_int)   == VAL_COEF[i]
                           && ($past(w_int)   - w_int)   == WGT_COEF[i]
                           && ($past(vol_int) - vol_int) == VOL_COEF[i] ) );
    end
  end
endmodule

// Bind into DUT (clockless checks always active; set USE_CLK=1 and connect TB clock for sequential checks/coverage)
bind var18_multi var18_multi_sva #(.USE_CLK(0)) u_var18_multi_sva (
  .clk(1'b0),
  .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G), .H(H), .I(I),
  .J(J), .K(K), .L(L), .M(M), .N(N), .O(O), .P(P), .Q(Q), .R(R),
  .valid(valid)
);