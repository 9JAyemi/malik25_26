// SVA for xor_module: checks sign/zero extension, XNOR function, X-prop, and covers key scenarios.

module xor_module_sva #(
  parameter int A_SIGNED = 0,
  parameter int B_SIGNED = 0,
  parameter int A_WIDTH  = 1,
  parameter int B_WIDTH  = 1,
  parameter int Y_WIDTH  = 1
) (
  input  logic [A_WIDTH-1:0]  A,
  input  logic [B_WIDTH-1:0]  B,
  input  logic [Y_WIDTH-1:0]  Y,
  input  logic [((A_WIDTH>B_WIDTH)?A_WIDTH:B_WIDTH)-1:0] A_buf,
  input  logic [((A_WIDTH>B_WIDTH)?A_WIDTH:B_WIDTH)-1:0] B_buf
);

  localparam int WIDTH = (A_WIDTH > B_WIDTH) ? A_WIDTH : B_WIDTH;

  // Expected sign/zero-extended operands and result
  logic [WIDTH-1:0] expA, expB, xnor_full;
  logic [Y_WIDTH-1:0] expY;

  assign expA = A_SIGNED ? {{WIDTH-A_WIDTH{A[A_WIDTH-1]}}, A} : {{WIDTH-A_WIDTH{1'b0}}, A};
  assign expB = B_SIGNED ? {{WIDTH-B_WIDTH{B[B_WIDTH-1]}}, B} : {{WIDTH-B_WIDTH{1'b0}}, B};
  assign xnor_full = ~(expA ^ expB);
  assign expY = xnor_full[Y_WIDTH-1:0];

  // Core functional check (when inputs are known), and X-prop on Y
  always @* begin
    if (!$isunknown({A,B})) begin
      assert (#0 (Y === expY)) else $error("xor_module: Y mismatch expY");
      assert (#0 (!$isunknown(Y))) else $error("xor_module: Y has X/Z with known inputs");
    end
  end

  // Internal extension correctness (also catches self-reference issues)
  always @* begin
    assert (#0 (A_buf === expA)) else $error("xor_module: A_buf extension mismatch");
    assert (#0 (B_buf === expB)) else $error("xor_module: B_buf extension mismatch");
    if (!$isunknown({A,B})) begin
      assert (#0 (!$isunknown({A_buf,B_buf}))) else $error("xor_module: A_buf/B_buf X/Z with known inputs");
    end
  end

  // Coverage: equality (all-ones), inequality, sign-extend corners, truncation activity
  cover property (@(posedge $global_clock)
    (!$isunknown({A,B})) && (expA == expB) && (Y == {Y_WIDTH{1'b1}})
  );
  cover property (@(posedge $global_clock)
    (!$isunknown({A,B})) && (expA != expB) && (Y != {Y_WIDTH{1'b1}})
  );

  if (A_SIGNED && (WIDTH > A_WIDTH)) begin
    cover property (@(posedge $global_clock) (A[A_WIDTH-1] == 1'b1) && (&expA[WIDTH-1:A_WIDTH]));
    cover property (@(posedge $global_clock) (A[A_WIDTH-1] == 1'b0) && (~|expA[WIDTH-1:A_WIDTH]));
  end
  if (B_SIGNED && (WIDTH > B_WIDTH)) begin
    cover property (@(posedge $global_clock) (B[B_WIDTH-1] == 1'b1) && (&expB[WIDTH-1:B_WIDTH]));
    cover property (@(posedge $global_clock) (B[B_WIDTH-1] == 1'b0) && (~|expB[WIDTH-1:B_WIDTH]));
  end
  if (Y_WIDTH < WIDTH) begin
    cover property (@(posedge $global_clock)
      (!$isunknown({A,B})) && (|xnor_full[WIDTH-1:Y_WIDTH])
    );
  end

endmodule

// Bind into DUT; connects to ports and internal A_buf/B_buf
bind xor_module xor_module_sva #(
  .A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED),
  .A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)
) xor_module_sva_i (
  .A(A), .B(B), .Y(Y), .A_buf(A_buf), .B_buf(B_buf)
);