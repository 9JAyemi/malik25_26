// SVA for sky130_fd_sc_hd__nand4b
// Function: Y = ~(B & C & D & ~A_N)

module sky130_fd_sc_hd__nand4b_sva (
  input logic Y,
  input logic A_N,
  input logic B,
  input logic C,
  input logic D
);

  // Sample on any input edge
  default clocking cb @(posedge A_N or negedge A_N
                      or posedge B   or negedge B
                      or posedge C   or negedge C
                      or posedge D   or negedge D); endclocking

  // Combinational functional check and X-check
  always_comb begin
    assert #0 (Y === ~(B & C & D & ~A_N))
      else $error("nand4b func mismatch: Y=%b A_N=%b B=%b C=%b D=%b", Y,A_N,B,C,D);
    if (!$isunknown({A_N,B,C,D}))
      assert #0 (!$isunknown(Y))
        else $error("nand4b: Y unknown with known inputs");
  end

  // Minimal, meaningful coverage
  // Only way to get Y==0
  cover property (~A_N & B & C & D & (Y==1'b0));
  // Independent causes for Y==1
  cover property ((A_N==1'b1) & (Y==1'b1));
  cover property ((A_N==1'b0) & (B==1'b0) &  C        &  D        & (Y==1'b1));
  cover property ((A_N==1'b0) &  B        & (C==1'b0) &  D        & (Y==1'b1));
  cover property ((A_N==1'b0) &  B        &  C        & (D==1'b0) & (Y==1'b1));

  // Y toggles both ways
  cover property (Y   ##1 !Y);
  cover property (!Y  ##1  Y);

endmodule

// Bind to the DUT
bind sky130_fd_sc_hd__nand4b sky130_fd_sc_hd__nand4b_sva sva_i (.*);