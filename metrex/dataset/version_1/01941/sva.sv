// SVA for sky130_fd_sc_ls__a31oi (Y = ~ (B1 | (A1 & A2 & A3)))

module sky130_fd_sc_ls__a31oi_sva (
  input logic A1, A2, A3, B1,
  input logic Y,
  input logic and0_out,
  input logic nor0_out_Y
);

  // Combinational functional checks (4-state accurate)
  always_comb begin
    assert #0 (and0_out   === (A1 & A2 & A3)) else $error("a31oi: AND3 mismatch");
    assert #0 (nor0_out_Y === ~(B1 | and0_out)) else $error("a31oi: NOR mismatch");
    assert #0 (Y          === nor0_out_Y) else $error("a31oi: BUF mismatch");
    assert #0 (Y          === ~(B1 | (A1 & A2 & A3))) else $error("a31oi: Y func mismatch");

    // If all inputs are known, Y must be known
    assert #0 ($isunknown({A1,A2,A3,B1}) || !$isunknown(Y))
      else $error("a31oi: Y X/Z with known inputs");
  end

  // Truth-table coverage: hit all 16 input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_VECTORS
      cover property (@(posedge A1 or negedge A1 or
                        posedge A2 or negedge A2 or
                        posedge A3 or negedge A3 or
                        posedge B1 or negedge B1)
                      {B1,A3,A2,A1} == i[3:0]);
    end
  endgenerate

  // Output value coverage
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1) Y == 1'b0);
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge A3 or negedge A3 or
                    posedge B1 or negedge B1) Y == 1'b1);

  // Per-input control coverage: show each input can toggle Y
  // B1 controls Y when A1&A2&A3==0
  cover property (@(posedge B1) $stable({A1,A2,A3}) && ((A1&A2&A3)==1'b0) ##0 (Y==1'b0));
  cover property (@(negedge B1) $stable({A1,A2,A3}) && ((A1&A2&A3)==1'b0) ##0 (Y==1'b1));
  // A1 controls Y when B1==0 and A2&A3==1
  cover property (@(posedge A1) $stable({A2,A3,B1}) && (B1==0) && ((A2&A3)==1) ##0 (Y==1'b0));
  cover property (@(negedge A1) $stable({A2,A3,B1}) && (B1==0) && ((A2&A3)==1) ##0 (Y==1'b1));
  // A2 controls Y when B1==0 and A1&A3==1
  cover property (@(posedge A2) $stable({A1,A3,B1}) && (B1==0) && ((A1&A3)==1) ##0 (Y==1'b0));
  cover property (@(negedge A2) $stable({A1,A3,B1}) && (B1==0) && ((A1&A3)==1) ##0 (Y==1'b1));
  // A3 controls Y when B1==0 and A1&A2==1
  cover property (@(posedge A3) $stable({A1,A2,B1}) && (B1==0) && ((A1&A2)==1) ##0 (Y==1'b0));
  cover property (@(negedge A3) $stable({A1,A2,B1}) && (B1==0) && ((A1&A2)==1) ##0 (Y==1'b1));

endmodule

// Bind into the DUT (connects internal nets for stage checks)
bind sky130_fd_sc_ls__a31oi sky130_fd_sc_ls__a31oi_sva u_a31oi_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y),
  .and0_out(and0_out), .nor0_out_Y(nor0_out_Y)
);