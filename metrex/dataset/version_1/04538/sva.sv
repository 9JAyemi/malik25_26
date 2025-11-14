// SystemVerilog Assertions for ad_addsub
// Focused, high-signal-coverage checks + concise end-to-end functional check.
// Bind into the DUT to access both ports and internal pipeline regs.

module ad_addsub_sva
  #(parameter int A_WIDTH = 32,
    parameter int ADD_SUB = 0,
    parameter logic [A_WIDTH-1:0] CONST_VALUE = 32'h1)
(
  input  logic                      clk,
  input  logic [A_WIDTH-1:0]        A,
  input  logic [A_WIDTH-1:0]        Amax,
  input  logic [A_WIDTH-1:0]        out,
  input  logic                      CE,

  // internal DUT signals (for deep pipeline checks)
  input  logic [A_WIDTH-1:0]        A_d,
  input  logic [A_WIDTH-1:0]        A_d2,
  input  logic [A_WIDTH-1:0]        Amax_d,
  input  logic [A_WIDTH-1:0]        Amax_d2,
  input  logic [A_WIDTH:0]          out_d,
  input  logic [A_WIDTH:0]          out_d2,
  input  logic [A_WIDTH-1:0]        B_reg
);

  localparam int ADDER       = 0;
  localparam int SUBSTRACTER = 1;

  // minimal warm-up for $past(,2)
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Basic sanity
  assert property (@(posedge clk) !$isunknown({CE, A, Amax}));
  assert property (@(posedge clk) B_reg == CONST_VALUE);

  // Pipeline alignment
  assert property (@(posedge clk) past1 |-> A_d    == $past(A));
  assert property (@(posedge clk) past2 |-> A_d2   == $past(A,2));
  assert property (@(posedge clk) past1 |-> Amax_d == $past(Amax));
  assert property (@(posedge clk) past2 |-> Amax_d2== $past(Amax,2));

  // Stage-1 arithmetic (sized exactly as RTL semantics)
  generate
    if (ADD_SUB == ADDER) begin : g_s1_add
      // out_d is zero-extended truncated sum
      assert property (@(posedge clk) out_d == {1'b0, (A_d + B_reg)});
      // carry bit is always 0 due to truncation in RTL
      assert property (@(posedge clk) out_d[A_WIDTH] == 1'b0);
    end else begin : g_s1_sub
      // out_d is zero-extended truncated difference
      assert property (@(posedge clk) out_d == {1'b0, (A_d - B_reg)});
      // MSB used as "borrow" flag in RTL is always 0 with current sizing
      assert property (@(posedge clk) out_d[A_WIDTH] == 1'b0);
    end
  endgenerate

  // Stage-2 wrap/adjust logic
  generate
    if (ADD_SUB == ADDER) begin : g_s2_add
      assert property (@(posedge clk)
        (out_d > {1'b0, Amax_d2}) |-> (out_d2 == (out_d - {1'b0, Amax_d2}))
      );
      assert property (@(posedge clk)
        !(out_d > {1'b0, Amax_d2}) |-> (out_d2 == out_d)
      );
      // Result is always <= Amax after adjust
      assert property (@(posedge clk) out_d2 <= {1'b0, Amax_d2});
    end else begin : g_s2_sub
      assert property (@(posedge clk)
        out_d[A_WIDTH] |-> (out_d2 == ({1'b0, Amax_d2} + out_d))
      );
      assert property (@(posedge clk)
        !out_d[A_WIDTH] |-> (out_d2 == out_d)
      );
    end
  endgenerate

  // Output stage gating
  assert property (@(posedge clk)  CE |-> (out == out_d2[A_WIDTH-1:0]));
  assert property (@(posedge clk) !CE |-> (out == '0));

  // End-to-end functional check using only ports ($past for pipeline timing)
  // Mirrors RTL sizing semantics exactly.
  generate
    if (ADD_SUB == ADDER) begin : g_e2e_add
      // s is A_WIDTH-wide sum (truncated), compare/wrap done at A_WIDTH+1
      assert property (@(posedge clk) past2 |->
        ( CE
          ? ( out ==
              ( ({1'b0, ($past(A)+CONST_VALUE)} > {1'b0, $past(Amax,2)})
                ? ( ({1'b0, ($past(A)+CONST_VALUE)} - {1'b0, $past(Amax,2)}) [A_WIDTH-1:0] )
                :   ($past(A)+CONST_VALUE)
              )
            )
          : (out == '0)
        )
      );
    end else begin : g_e2e_sub
      // t is A_WIDTH-wide difference (truncated); no wrap occurs per RTL
      assert property (@(posedge clk) past1 |->
        ( CE ? (out == ($past(A)-CONST_VALUE)) : (out == '0) )
      );
    end
  endgenerate

  // Targeted coverage
  generate
    if (ADD_SUB == ADDER) begin : g_cov_add
      // Cover both add paths (no-wrap and wrap)
      cover property (@(posedge clk) past2 &&
        ({1'b0, ($past(A)+CONST_VALUE)} <= {1'b0, $past(Amax,2)}) && CE);
      cover property (@(posedge clk) past2 &&
        ({1'b0, ($past(A)+CONST_VALUE)} >  {1'b0, $past(Amax,2)}) && CE);
    end else begin : g_cov_sub
      // Try to see a "borrow" (will likely never hit with current sizing)
      cover property (@(posedge clk) past1 && ($past(A) < CONST_VALUE) && CE);
    end
  endgenerate

  // CE activity coverage
  cover property (@(posedge clk) $rose(CE));
  cover property (@(posedge clk) $fell(CE));

endmodule

// Bind into DUT (connect ports and internal regs)
bind ad_addsub ad_addsub_sva #(
  .A_WIDTH   (A_WIDTH),
  .ADD_SUB   (ADD_SUB),
  .CONST_VALUE(CONST_VALUE)
) i_ad_addsub_sva (
  .clk       (clk),
  .A         (A),
  .Amax      (Amax),
  .out       (out),
  .CE        (CE),
  .A_d       (A_d),
  .A_d2      (A_d2),
  .Amax_d    (Amax_d),
  .Amax_d2   (Amax_d2),
  .out_d     (out_d),
  .out_d2    (out_d2),
  .B_reg     (B_reg)
);