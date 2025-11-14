// SVA for sky130_fd_sc_hd__and4b
// Function: X = (~A_N) & B & C & D

module sky130_fd_sc_hd__and4b_sva (
  input logic A_N,
  input logic B,
  input logic C,
  input logic D,
  input logic X
);

  // Immediate, zero-delay functional check and X/Z sanitization
  always_comb begin
    assert #0 (!$isunknown({A_N,B,C,D,X}))
      else $error("AND4B: X or inputs are X/Z");
    assert #0 (X === ((~A_N) & B & C & D))
      else $error("AND4B: Functional mismatch: X != (~A_N)&B&C&D");
  end

  // Concurrent equivalence in both directions on any input/output edge
  property p_clk_ev;
    @(posedge A_N or negedge A_N or
      posedge B   or negedge B   or
      posedge C   or negedge C   or
      posedge D   or negedge D   or
      posedge X   or negedge X)
      1;
  endproperty

  // X implies all enabling inputs true
  assert property (p_clk_ev |-> (X |-> (~A_N & B & C & D)));
  // All enabling inputs true implies X
  assert property (p_clk_ev |-> ((~A_N & B & C & D) |-> X));

  // Basic output polarity covers
  cover property (p_clk_ev and X==1);
  cover property (p_clk_ev and X==0);

  // Truth-table coverage (all 16 input combinations observed)
  genvar i;
  for (i = 0; i < 16; i++) begin : g_tt
    localparam logic [3:0] V = i[3:0];
    cover property (
      @(posedge A_N or negedge A_N or
        posedge B   or negedge B   or
        posedge C   or negedge C   or
        posedge D   or negedge D)
      {A_N,B,C,D} == V
    );
  end

  // Cause-effect covers: each input controls X when others enable it
  cover property (@(posedge B or negedge B) (!A_N && C && D) ##0 (X == B));
  cover property (@(posedge C or negedge C) (!A_N && B && D) ##0 (X == C));
  cover property (@(posedge D or negedge D) (!A_N && B && C) ##0 (X == D));
  cover property (@(posedge A_N or negedge A_N) (B && C && D) ##0 (X == ~A_N));

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__and4b sky130_fd_sc_hd__and4b_sva i_and4b_sva (
  .A_N(A_N), .B(B), .C(C), .D(D), .X(X)
);