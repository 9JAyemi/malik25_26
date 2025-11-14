// SVA checker for var20_multi
// Bind example (edit clock/reset paths to your TB):
// bind var20_multi var20_multi_sva u_var20_multi_sva (
//   .clk(tb.clk), .rst_n(tb.rst_n),
//   .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G), .H(H), .I(I), .J(J),
//   .K(K), .L(L), .M(M), .N(N), .O(O), .P(P), .Q(Q), .R(R), .S(S), .T(T),
//   .total_value(total_value), .total_weight(total_weight), .total_volume(total_volume),
//   .valid(valid)
// );

module var20_multi_sva (
  input  logic clk, rst_n,
  input  logic A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T,
  input  logic [8:0] total_value, total_weight, total_volume,
  input  logic       valid
);

  // constants
  localparam logic [8:0] MIN_VALUE  = 9'd120;
  localparam logic [8:0] MAX_WEIGHT = 9'd60;
  localparam logic [8:0] MAX_VOLUME = 9'd60;

  localparam logic [8:0] VAL [20] = '{9'd4,9'd8,9'd0,9'd20,9'd10,9'd12,9'd18,9'd14,9'd6,9'd15,
                                      9'd30,9'd8,9'd16,9'd18,9'd18,9'd14,9'd7,9'd7,9'd29,9'd23};
  localparam logic [8:0] WGT [20] = '{9'd28,9'd8,9'd27,9'd18,9'd27,9'd28,9'd6,9'd1,9'd20,9'd0,
                                      9'd5,9'd13,9'd8,9'd14,9'd22,9'd12,9'd23,9'd26,9'd1,9'd22};
  localparam logic [8:0] VOL [20] = '{9'd27,9'd27,9'd4,9'd4,9'd0,9'd24,9'd4,9'd20,9'd12,9'd15,
                                      9'd5,9'd2,9'd9,9'd28,9'd19,9'd18,9'd30,9'd12,9'd28,9'd13};

  localparam logic [8:0] MAX_TVAL = 9'd277;
  localparam logic [8:0] MAX_TWGT = 9'd309;
  localparam logic [8:0] MAX_TVOL = 9'd301;

  // pack inputs as MSB=A ... LSB=T
  logic [19:0] ibits;
  assign ibits = {A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T};

  // expected totals (recomputed)
  logic [8:0] exp_value, exp_weight, exp_volume;
  integer i;
  always_comb begin
    exp_value  = '0;
    exp_weight = '0;
    exp_volume = '0;
    for (i = 0; i < 20; i++) begin
      if (ibits[19-i]) begin
        exp_value  += VAL[i];
        exp_weight += WGT[i];
        exp_volume += VOL[i];
      end
    end
  end

  // Combinational correctness and X checks
  always_comb begin
    assert (!$isunknown({A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T}))
      else $error("var20_multi: X/Z on inputs");
    assert (!$isunknown({total_value,total_weight,total_volume,valid}))
      else $error("var20_multi: X/Z on totals/valid");

    assert (total_value  == exp_value)
      else $error("var20_multi: total_value mismatch");
    assert (total_weight == exp_weight)
      else $error("var20_multi: total_weight mismatch");
    assert (total_volume == exp_volume)
      else $error("var20_multi: total_volume mismatch");

    assert (valid === ((total_value >= MIN_VALUE) && (total_weight <= MAX_WEIGHT) && (total_volume <= MAX_VOLUME)))
      else $error("var20_multi: valid computation mismatch");

    assert (total_value  <= MAX_TVAL) else $error("var20_multi: total_value overflow");
    assert (total_weight <= MAX_TWGT) else $error("var20_multi: total_weight overflow");
    assert (total_volume <= MAX_TVOL) else $error("var20_multi: total_volume overflow");
  end

  // Single-bit toggle delta checks (rise/fall), guarded for exactly-one-bit change
  genvar gi;
  generate
    for (gi = 0; gi < 20; gi++) begin : g_deltas
      localparam int SHIFT = 19-gi;

      // single-bit rise on item gi
      property p_item_rise;
        @(posedge clk) disable iff (!rst_n)
          !$isunknown({ibits, total_value,total_weight,total_volume}) &&
          ((ibits ^ $past(ibits)) == (20'b1 << SHIFT)) && ibits[SHIFT] && !$past(ibits[SHIFT])
          |-> (total_value  == $past(total_value)  + VAL[gi]) &&
              (total_weight == $past(total_weight) + WGT[gi]) &&
              (total_volume == $past(total_volume) + VOL[gi]);
      endproperty
      assert property (p_item_rise);

      // single-bit fall on item gi
      property p_item_fall;
        @(posedge clk) disable iff (!rst_n)
          !$isunknown({ibits, total_value,total_weight,total_volume}) &&
          ((ibits ^ $past(ibits)) == (20'b1 << SHIFT)) && !ibits[SHIFT] && $past(ibits[SHIFT])
          |-> ($past(total_value)  == total_value  + VAL[gi]) &&
              ($past(total_weight) == total_weight + WGT[gi]) &&
              ($past(total_volume) == total_volume + VOL[gi]);
      endproperty
      assert property (p_item_fall);

      // cover: observe single-bit toggle
      cover property (@(posedge clk) ((ibits ^ $past(ibits)) == (20'b1 << SHIFT)));
    end
  endgenerate

  // Valid boundary coverage
  cover property (@(posedge clk) valid);
  cover property (@(posedge clk) !valid);

  cover property (@(posedge clk) (exp_value  == MIN_VALUE)  && (exp_weight <= MAX_WEIGHT) && (exp_volume <= MAX_VOLUME));
  cover property (@(posedge clk) (exp_value  == MIN_VALUE-1) && (exp_weight <= MAX_WEIGHT) && (exp_volume <= MAX_VOLUME));
  cover property (@(posedge clk) (exp_weight == MAX_WEIGHT) && (exp_value  >= MIN_VALUE)  && (exp_volume <= MAX_VOLUME));
  cover property (@(posedge clk) (exp_volume == MAX_VOLUME) && (exp_value  >= MIN_VALUE)  && (exp_weight <= MAX_WEIGHT));

  // Extremes
  cover property (@(posedge clk) (exp_value  == MAX_TVAL));
  cover property (@(posedge clk) (exp_weight == MAX_TWGT));
  cover property (@(posedge clk) (exp_volume == MAX_TVOL));

endmodule