// SVA for _90_pmux2: parameterized priority-mux (OR-of-selected slices; A when no select)
// Bind this file to the DUT to check and cover functional behavior.

module pmux2_sva #(
  parameter int WIDTH = 1,
  parameter int S_WIDTH = 1
)(
  input  logic [WIDTH-1:0]            A,
  input  logic [WIDTH*S_WIDTH-1:0]    B,
  input  logic [S_WIDTH-1:0]          S,
  input  logic [WIDTH-1:0]            Y
);

  // Sanity of parameters
  initial begin
    assert (WIDTH   > 0) else $fatal(1, "WIDTH must be > 0");
    assert (S_WIDTH > 0) else $fatal(1, "S_WIDTH must be > 0");
  end

  // Helper: OR-reduce selected B slices according to S
  function automatic logic [WIDTH-1:0] or_select
    (input logic [WIDTH*S_WIDTH-1:0] b, input logic [S_WIDTH-1:0] s);
    logic [WIDTH-1:0] acc;
    acc = '0;
    for (int i = 0; i < S_WIDTH; i++) begin
      if (s[i]) acc |= b[i*WIDTH +: WIDTH];
    end
    return acc;
  endfunction

  function automatic logic [WIDTH-1:0] expected_y
    (input logic [WIDTH-1:0] a,
     input logic [WIDTH*S_WIDTH-1:0] b,
     input logic [S_WIDTH-1:0] s);
    return (|s) ? or_select(b, s) : a;
  endfunction

  // Core functional equivalence (4-state exact)
  always_comb begin
    logic [WIDTH-1:0] exp = expected_y(A, B, S);
    assert (Y === exp)
      else $error("pmux2 mismatch: Y=%0h exp=%0h A=%0h S=%0h B=%0h",
                  Y, exp, A, S, B);
  end

  // X/Z cleanliness: clean inputs must produce clean output
  always_comb begin
    if (!$isunknown({A, B, S})) begin
      assert (!$isunknown(Y))
        else $error("pmux2 X/Z propagation: Y unknown with clean inputs. A=%0h S=%0h B=%0h", A, S, B);
    end
  end

  // Special-case checks to aid debug
  //  - No selects: Y == A
  always_comb if (S == '0) assert (Y === A)
    else $error("pmux2: S==0 but Y!=A (Y=%0h A=%0h)", Y, A);

  //  - One-hot selects: Y == selected B slice
  genvar gi;
  generate
    for (gi = 0; gi < S_WIDTH; gi++) begin : g_onehot_chk
      localparam logic [S_WIDTH-1:0] ONE = ({{(S_WIDTH-1){1'b0}},1'b1} << gi);
      always_comb if (S == ONE) assert (Y === B[gi*WIDTH +: WIDTH])
        else if (S == ONE) $error("pmux2: one-hot S[%0d]=1 but Y!=B[%0d] (Y=%0h Bsel=%0h)",
                                  gi, gi, Y, B[gi*WIDTH +: WIDTH]);
    end
  endgenerate

  //  - Multi-selects: Y == OR of selected slices
  always_comb if ($countones(S) > 1) assert (Y === or_select(B, S))
    else if ($countones(S) > 1) $error("pmux2: multi-select but Y!=OR(B_sel)");

  // Lightweight coverage
  //  - Cover no-select, each one-hot select, multi-select
  always_comb begin
    cover (S == '0);
    for (int i = 0; i < S_WIDTH; i++) cover (S == (1 << i));
    cover ($countones(S) > 1);
  end

  // Optional: cover that output follows A when no select, and follows B slice on each one-hot
  always_comb begin
    cover ((S == '0) && (Y === A));
    for (int i = 0; i < S_WIDTH; i++) begin
      cover ((S == (1 << i)) && (Y === B[i*WIDTH +: WIDTH]));
    end
  end

endmodule

// Bind into DUT instances
bind _90_pmux2 pmux2_sva #(.WIDTH(WIDTH), .S_WIDTH(S_WIDTH)) _pmux2_sva_bind (.A(A), .B(B), .S(S), .Y(Y));