// SVA for sky130_fd_sc_hs__nand4bb
// Function: Y === ~(A_N & B_N & C & D)

module sky130_fd_sc_hs__nand4bb_sva (
  input logic Y,
  input logic A_N,
  input logic B_N,
  input logic C,
  input logic D
);

  // Sample on any input edge; check zero-delay combinational correctness
  property p_func_nand4bb;
    @(posedge A_N or negedge A_N or
      posedge B_N or negedge B_N or
      posedge C   or negedge C   or
      posedge D   or negedge D)
      ##0 (Y === ~(A_N & B_N & C & D));
  endproperty
  assert property (p_func_nand4bb)
    else $error("nand4bb mismatch: Y=%b A_N=%b B_N=%b C=%b D=%b", Y, A_N, B_N, C, D);

  // Minimal but full input-space coverage (all 16 combos observed)
  genvar i;
  for (i = 0; i < 16; i++) begin : gen_cov_inputs
    cover property (
      @(posedge A_N or negedge A_N or
        posedge B_N or negedge B_N or
        posedge C   or negedge C   or
        posedge D   or negedge D)
      ##0 ({A_N,B_N,C,D} == i[3:0])
    );
  end

  // Output toggle coverage
  cover property (@(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D) $rose(Y));
  cover property (@(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D) $fell(Y));

endmodule

// Bind into DUT
bind sky130_fd_sc_hs__nand4bb sky130_fd_sc_hs__nand4bb_sva u_nand4bb_sva (.*);