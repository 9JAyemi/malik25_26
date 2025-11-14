// SVA for alu: bind this module to the DUT. Provide clk and rst_n from your environment.
module alu_sva #(
  parameter A_SIGNED = 0,
  parameter B_SIGNED = 0,
  parameter A_WIDTH  = 1,
  parameter B_WIDTH  = 1,
  parameter Y_WIDTH  = 1
)(
  input  logic                         clk,
  input  logic                         rst_n,
  input  logic [A_WIDTH-1:0]          A,
  input  logic [B_WIDTH-1:0]          B,
  input  logic                        BI,
  input  logic [Y_WIDTH-1:0]          X,
  input  logic [Y_WIDTH-1:0]          CO
);

  localparam int AW = A_WIDTH;
  localparam int BW = B_WIDTH;
  localparam int YW = Y_WIDTH;

  // Resize A and B to Y_WIDTH using sign/zero extension per params. Truncate if narrower Y.
  logic [YW-1:0] A_ext, B_ext;

  generate
    if (YW >= AW) begin : g_extA_up
      if (A_SIGNED) begin : g_extA_s
        assign A_ext = {{(YW-AW){A[AW-1]}}, A};
      end else begin : g_extA_u
        assign A_ext = {{(YW-AW){1'b0}}, A};
      end
    end else begin : g_extA_down
      assign A_ext = A[YW-1:0];
    end
  endgenerate

  generate
    if (YW >= BW) begin : g_extB_up
      if (B_SIGNED) begin : g_extB_s
        assign B_ext = {{(YW-BW){B[BW-1]}}, B};
      end else begin : g_extB_u
        assign B_ext = {{(YW-BW){1'b0}}, B};
      end
    end else begin : g_extB_down
      assign B_ext = B[YW-1:0];
    end
  endgenerate

  // Full-width arithmetic for result and carry/borrow
  logic [YW:0] add_full, sub_full;
  assign add_full = {1'b0, A_ext} + {1'b0, B_ext};
  assign sub_full = {1'b0, A_ext} - {1'b0, B_ext};

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No-X on outputs when inputs are known
  assert property (!$isunknown({A,B,BI})) |-> !$isunknown({X,CO}));

  // Functional correctness of X and CO (CO replicated across all bits)
  assert property ( !BI |-> ( X == add_full[YW-1:0] && CO == {YW{add_full[YW]}} ) );
  assert property (  BI |-> ( X == sub_full[YW-1:0] && CO == {YW{sub_full[YW]}} ) );

  // CO bits must be identical (detects bus-width CO driven by a single bit inconsistently)
  assert property (CO == {YW{CO[0]}});

  // Minimal, meaningful coverage
  cover property ( !BI && add_full[YW] );      // addition with carry
  cover property ( !BI && !add_full[YW] );     // addition without carry
  cover property (  BI && sub_full[YW] );      // subtraction with borrow
  cover property (  BI && !sub_full[YW] );     // subtraction without borrow

endmodule

// Bind example (replace clk/rst_n with your environment signals)
bind alu alu_sva #(
  .A_SIGNED(A_SIGNED),
  .B_SIGNED(B_SIGNED),
  .A_WIDTH (A_WIDTH),
  .B_WIDTH (B_WIDTH),
  .Y_WIDTH (Y_WIDTH)
) i_alu_sva (
  .clk  (clk),
  .rst_n(rst_n),
  .A    (A),
  .B    (B),
  .BI   (BI),
  .X    (X),
  .CO   (CO)
);