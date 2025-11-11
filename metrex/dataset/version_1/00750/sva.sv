// SVA for sky130_fd_sc_ls__a2bb2oi
`ifndef SKY130_FD_SC_LS__A2BB2OI_SVA
`define SKY130_FD_SC_LS__A2BB2OI_SVA

module sky130_fd_sc_ls__a2bb2oi_sva (
  input logic Y,
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2,
  input logic and0_out,
  input logic nor0_out,
  input logic nor1_out_Y
);

  // Functional and internal net equivalence with X-safety
  always_comb begin
    if (!$isunknown({A1_N,A2_N,B1,B2})) begin
      assert (Y === (~((~(A1_N | A2_N)) | (B1 & B2))))
        else $error("Y functional mismatch");
      assert (!$isunknown(Y))
        else $error("Y is X/Z while inputs are known");

      assert (and0_out  === (B1 & B2))
        else $error("and0_out != B1&B2");
      assert (nor0_out  === ~(A1_N | A2_N))
        else $error("nor0_out != ~(A1_N|A2_N)");
      assert (nor1_out_Y === ~(nor0_out | and0_out))
        else $error("nor1_out_Y != ~(nor0_out|and0_out)");
      assert (Y === nor1_out_Y)
        else $error("buf path mismatch: Y != nor1_out_Y");

      // Sanity implications (helpful in 4-state sims)
      if (~(A1_N | A2_N)) assert (Y === 1'b0) else $error("Y must be 0 when ~(A1_N|A2_N)");
      if (B1 & B2)        assert (Y === 1'b0) else $error("Y must be 0 when B1&B2");
    end
  end

  // Coverage: output values, internal nodes, and edges
  always_comb begin
    cover (!$isunknown({A1_N,A2_N,B1,B2}) && (Y==1'b1));
    cover (!$isunknown({A1_N,A2_N,B1,B2}) && (Y==1'b0));
    cover (and0_out);
    cover (nor0_out);
    cover (and0_out && nor0_out);
    cover (!and0_out && !nor0_out);
  end

  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);
  cover property (@(posedge A1_N) 1);
  cover property (@(negedge A1_N) 1);
  cover property (@(posedge A2_N) 1);
  cover property (@(negedge A2_N) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge B2) 1);
  cover property (@(negedge B2) 1);

endmodule

bind sky130_fd_sc_ls__a2bb2oi sky130_fd_sc_ls__a2bb2oi_sva u_sva (
  .Y(Y),
  .A1_N(A1_N),
  .A2_N(A2_N),
  .B1(B1),
  .B2(B2),
  .and0_out(and0_out),
  .nor0_out(nor0_out),
  .nor1_out_Y(nor1_out_Y)
);

`endif