// SVA for decoder_4to16
// Concise checks for functional correctness, X-propagation, and coverage.
// Bind into the DUT as shown at the end.

module decoder_4to16_sva (
  input  logic [1:0] A, B,
  input  logic       EN,
  input  logic [15:0] Y
);
  logic [1:0] sel;
  assign sel = {A,B};

  logic [15:0] exp_y_en;
  assign exp_y_en = 16'hFFFF ^ (16'h0001 << sel); // active-low one-hot in [3:0]

  // Functional mapping: on any input change, output matches expected after delta
  property p_func;
    @(A or B or EN) 1'b1 |-> ##0 (Y == (EN ? exp_y_en : 16'hFFFF));
  endproperty
  assert property (p_func);

  // Upper bits [15:4] must always be 1s
  assert property (@(A or B or EN) 1'b1 |-> ##0 (Y[15:4] == 12'hFFF));

  // When enabled, exactly one 0 in Y[3:0] and it matches sel
  assert property (@(A or B or EN) EN |-> ##0 ((~Y[3:0]) == (4'b0001 << sel)));

  // No X/Z on Y when inputs are known
  assert property (@(A or B or EN) (!$isunknown({A,B,EN})) |-> ##0 (!$isunknown(Y)));

  // Coverage: EN=0 case and each decode when EN=1
  cover property (@(A or B or EN) !EN ##0 (Y == 16'hFFFF));
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : c_decodes
      cover property (@(A or B or EN) EN && sel == i ##0 (Y == (16'hFFFF ^ (16'h0001 << i))));
    end
  endgenerate
endmodule

bind decoder_4to16 decoder_4to16_sva (.A(A), .B(B), .EN(EN), .Y(Y));