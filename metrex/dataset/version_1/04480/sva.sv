// SVA for var24_multi
// Bind this inside the DUT and drive clk/rst_n from your environment.

module var24_multi_sva (input logic clk, input logic rst_n);
  // Access DUT signals via bind (A..X, totals, thresholds, valid)
  wire [23:0] iv = {A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X};

  // Recompute expected totals (golden)
  wire [8:0] exp_total_value =
        A * 9'd4  + B * 9'd8  + C * 9'd0  + D * 9'd20 + E * 9'd10 + F * 9'd12
      + G * 9'd18 + H * 9'd14 + I * 9'd6  + J * 9'd15 + K * 9'd30 + L * 9'd8
      + M * 9'd16 + N * 9'd18 + O * 9'd18 + P * 9'd14 + Q * 9'd7  + R * 9'd7
      + S * 9'd29 + T * 9'd23 + U * 9'd24 + V * 9'd3  + W * 9'd18 + X * 9'd5;

  wire [8:0] exp_total_weight =
        A * 9'd28 + B * 9'd8  + C * 9'd27 + D * 9'd18 + E * 9'd27 + F * 9'd28
      + G * 9'd6  + H * 9'd1  + I * 9'd20 + J * 9'd0  + K * 9'd5  + L * 9'd13
      + M * 9'd8  + N * 9'd14 + O * 9'd22 + P * 9'd12 + Q * 9'd23 + R * 9'd26
      + S * 9'd1  + T * 9'd22 + U * 9'd26 + V * 9'd15 + W * 9'd0  + X * 9'd21;

  wire [8:0] exp_total_volume =
        A * 9'd27 + B * 9'd27 + C * 9'd4  + D * 9'd4  + E * 9'd0  + F * 9'd24
      + G * 9'd4  + H * 9'd20 + I * 9'd12 + J * 9'd15 + K * 9'd5  + L * 9'd2
      + M * 9'd9  + N * 9'd28 + O * 9'd19 + P * 9'd18 + Q * 9'd30 + R * 9'd12
      + S * 9'd28 + T * 9'd13 + U * 9'd18 + V * 9'd16 + W * 9'd26 + X * 9'd3;

  localparam int MAX_VAL = 327;
  localparam int MAX_W   = 371;
  localparam int MAX_V   = 364;

  default clocking cb @(posedge clk); endclocking

  // Constant sanity
  assert property (cb disable iff (!rst_n)
    (min_value == 9'd120) && (max_weight == 9'd60) && (max_volume == 9'd60));

  // No X-propagation: known inputs -> known combinational outputs
  assert property (cb disable iff (!rst_n)
    !$isunknown(iv) |-> !$isunknown({total_value,total_weight,total_volume,valid}));

  // Totals correct
  assert property (cb disable iff (!rst_n)
    int'(total_value) == int'(exp_total_value) &&
    int'(total_weight) == int'(exp_total_weight) &&
    int'(total_volume) == int'(exp_total_volume));

  // Totals never exceed theoretical maxima
  assert property (cb disable iff (!rst_n)
    (int'(total_value) <= MAX_VAL) &&
    (int'(total_weight) <= MAX_W) &&
    (int'(total_volume) <= MAX_V));

  // valid definition
  assert property (cb disable iff (!rst_n)
    valid == ((total_value >= min_value) &&
              (total_weight <= max_weight) &&
              (total_volume <= max_volume)));

  // Single-bit delta checks (only one input toggles in a cycle)
`define DELTA(sig,dv,dw,dvol) \
  assert property (cb disable iff (!rst_n) \
    $rose(sig) && $onehot(iv ^ $past(iv)) |-> \
      int'(total_value) == int'($past(total_value)) + (dv) && \
      int'(total_weight) == int'($past(total_weight)) + (dw) && \
      int'(total_volume) == int'($past(total_volume)) + (dvol)); \
  assert property (cb disable iff (!rst_n) \
    $fell(sig) && $onehot(iv ^ $past(iv)) |-> \
      int'(total_value) == int'($past(total_value)) - (dv) && \
      int'(total_weight) == int'($past(total_weight)) - (dw) && \
      int'(total_volume) == int'($past(total_volume)) - (dvol));

  `DELTA(A, 9'd4 , 9'd28, 9'd27)
  `DELTA(B, 9'd8 , 9'd8 , 9'd27)
  `DELTA(C, 9'd0 , 9'd27, 9'd4 )
  `DELTA(D, 9'd20, 9'd18, 9'd4 )
  `DELTA(E, 9'd10, 9'd27, 9'd0 )
  `DELTA(F, 9'd12, 9'd28, 9'd24)
  `DELTA(G, 9'd18, 9'd6 , 9'd4 )
  `DELTA(H, 9'd14, 9'd1 , 9'd20)
  `DELTA(I, 9'd6 , 9'd20, 9'd12)
  `DELTA(J, 9'd15, 9'd0 , 9'd15)
  `DELTA(K, 9'd30, 9'd5 , 9'd5 )
  `DELTA(L, 9'd8 , 9'd13, 9'd2 )
  `DELTA(M, 9'd16, 9'd8 , 9'd9 )
  `DELTA(N, 9'd18, 9'd14, 9'd28)
  `DELTA(O, 9'd18, 9'd22, 9'd19)
  `DELTA(P, 9'd14, 9'd12, 9'd18)
  `DELTA(Q, 9'd7 , 9'd23, 9'd30)
  `DELTA(R, 9'd7 , 9'd26, 9'd12)
  `DELTA(S, 9'd29, 9'd1 , 9'd28)
  `DELTA(T, 9'd23, 9'd22, 9'd13)
  `DELTA(U, 9'd24, 9'd26, 9'd18)
  `DELTA(V, 9'd3 , 9'd15, 9'd16)
  `DELTA(W, 9'd18, 9'd0 , 9'd26)
  `DELTA(X, 9'd5 , 9'd21, 9'd3 )
`undef DELTA

  // Functional coverage
  cover property (cb disable iff (!rst_n) valid);
  cover property (cb disable iff (!rst_n) !valid);
  cover property (cb disable iff (!rst_n)
    (total_value == min_value) && (total_weight <= max_weight) &&
    (total_volume <= max_volume) && valid);
  cover property (cb disable iff (!rst_n)
    (total_weight == max_weight) && (total_value >= min_value) &&
    (total_volume <= max_volume) && valid);
  cover property (cb disable iff (!rst_n)
    (total_volume == max_volume) && (total_value >= min_value) &&
    (total_weight <= max_weight) && valid);
  cover property (cb disable iff (!rst_n)
    (total_value < min_value) && (total_weight <= max_weight) &&
    (total_volume <= max_volume) && !valid);
  cover property (cb disable iff (!rst_n)
    (total_value >= min_value) && (total_weight > max_weight) &&
    (total_volume <= max_volume) && !valid);
  cover property (cb disable iff (!rst_n)
    (total_value >= min_value) && (total_weight <= max_weight) &&
    (total_volume > max_volume) && !valid);
  cover property (cb disable iff (!rst_n) (iv == '0));
  cover property (cb disable iff (!rst_n) (iv == '1));
  cover property (cb disable iff (!rst_n) $onehot(iv ^ $past(iv)));
endmodule

// Example bind (edit clock/reset to your env):
// bind var24_multi var24_multi_sva sva(.clk(clk), .rst_n(rst_n));