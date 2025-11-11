// SVA binder for generic_baseblocks_v2_1_mux_enc
// Concise, high-quality checks and coverage
bind generic_baseblocks_v2_1_mux_enc
module generic_baseblocks_v2_1_mux_enc_sva
  #(
    parameter string  C_FAMILY     = "rtl",
    parameter int     C_RATIO      = 4,
    parameter int     C_SEL_WIDTH  = 2,
    parameter int     C_DATA_WIDTH = 1
  )
  (
    input  wire [C_SEL_WIDTH-1:0]          S,
    input  wire [C_RATIO*C_DATA_WIDTH-1:0] A,
    input  wire [C_DATA_WIDTH-1:0]         O,
    input  wire                            OE
  );

  localparam int SW = C_SEL_WIDTH;
  localparam int DW = C_DATA_WIDTH;
  localparam int R  = C_RATIO;

  // Elaboration-time parameter sanity
  initial begin
    assert (R >= 1) else $error("%m: C_RATIO must be >=1");
    assert (DW >= 1) else $error("%m: C_DATA_WIDTH must be >=1");
    assert (SW >= ((R<=1)?1:$clog2(R))) else
      $error("%m: C_SEL_WIDTH (%0d) insufficient for C_RATIO (%0d)", SW, R);
  end

  // Helper: compute expected data for given S and A
  function automatic logic [DW-1:0] exp_data
    (input logic [SW-1:0] s, input logic [R*DW-1:0] a);
    int unsigned idx;
    begin
      if ($isunknown(s)) begin
        exp_data = '0; // guarded by known-inputs in assertions
      end else begin
        idx = s;
        exp_data = (idx < R) ? a[idx*DW +: DW] : '0;
      end
    end
  endfunction

  // Gating must force O to zero when OE==0, regardless of A/S/X
  always_comb begin
    if (OE === 1'b0) assert (O === '0)
      else $error("%m: OE==0 but O!=0");
  end

  // Functional correctness: when inputs are known, enforce mux semantics
  always_comb begin
    if (!$isunknown({S, A, OE})) begin
      logic [DW-1:0] exp = exp_data(S, A);
      assert (O === (OE ? exp : '0))
        else $error("%m: MUX mismatch. S=%0d OE=%0b EXP=%0h O=%0h", S, OE, exp, O);
      assert (!$isunknown(O))
        else $error("%m: Known inputs produced X/Z on O");
    end
  end

  // Coverage: hit each legal select value with OE high and correct data on O
  genvar i;
  generate
    for (i = 0; i < R; i++) begin : cov_sel
      localparam logic [SW-1:0] I_SEL = i[SW-1:0];
      always_comb
        cover (OE && !$isunknown({S,A}) && (S == I_SEL) &&
               (O === A[i*DW +: DW]));
    end
  endgenerate

  // Coverage: exercise out-of-range select codes (if any) with OE high -> O==0
  // Also covers power-of-two gaps in S space
  always_comb
    cover (OE && !$isunknown({S,A}) &&
           (int'(S) >= R) && (O === '0));

  // Coverage: OE low case
  always_comb
    cover ((OE === 1'b0) && (O === '0));

endmodule