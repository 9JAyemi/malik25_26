// SVA for sky130_fd_sc_hd__nor4bb
// Function: Y = (~(A | B)) & C_N & D_N
// Concise, bindable, clockless checks + coverage

`ifndef SKY130_FD_SC_HD__NOR4BB_SVA
`define SKY130_FD_SC_HD__NOR4BB_SVA

module sky130_fd_sc_hd__nor4bb_sva (
  input logic A, B, C_N, D_N,
  input logic Y,
  // bind to internals for structural sanity
  input logic nor0_out,
  input logic and0_out_Y
);

  // Sample on any relevant edge
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge C_N or negedge C_N or
      posedge D_N or negedge D_N or
      posedge Y or negedge Y
  ); endclocking

  // Golden combinational function (delta-cycle settle)
  assert property (1'b1 |-> ##0 (Y === ((~(A|B)) & C_N & D_N)))
    else $error("Y func mismatch: Y=%b A=%b B=%b C_N=%b D_N=%b", Y,A,B,C_N,D_N);

  // Internal structural checks
  assert property (1'b1 |-> ##0 (nor0_out   === ~(A|B)))
    else $error("nor0_out mismatch");
  assert property (1'b1 |-> ##0 (and0_out_Y === (nor0_out & C_N & D_N)))
    else $error("and0_out_Y mismatch");
  assert property (1'b1 |-> ##0 (Y === and0_out_Y))
    else $error("buf mismatch");

  // Deterministic-0 dominance (robust to X on non-dominant inputs)
  assert property ((A===1 || B===1 || C_N===0 || D_N===0) |-> ##0 (Y===1'b0))
    else $error("Dominance violated: Y not 0 under forcing condition");

  // Deterministic-1 minterm
  assert property ((A===0 && B===0 && C_N===1 && D_N===1) |-> ##0 (Y===1'b1))
    else $error("One-mintem violated: Y not 1 when A=0,B=0,C_N=1,D_N=1");

  // Knownness: if all inputs are known, output must be known
  assert property ((!$isunknown({A,B,C_N,D_N})) |-> ##0 (!$isunknown(Y)))
    else $error("Y unknown while inputs known");

  // Y should never be 'z'
  assert property (1'b1 |-> ##0 (Y !== 1'bz))
    else $error("Y is Z");

  // Functional coverage: all 16 input combinations with expected Y
  cover property (({A,B,C_N,D_N}===4'b0000) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0001) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0010) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0011) && (Y===1'b1)); // only 1 case Y=1
  cover property (({A,B,C_N,D_N}===4'b0100) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0101) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0110) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b0111) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1000) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1001) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1010) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1011) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1100) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1101) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1110) && (Y===1'b0));
  cover property (({A,B,C_N,D_N}===4'b1111) && (Y===1'b0));

  // Output activity coverage
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Transition coverage for each dominant edge causing Y to 0
  cover property ($rose(A)   ##0 (Y===1'b0));
  cover property ($rose(B)   ##0 (Y===1'b0));
  cover property ($fell(C_N) ##0 (Y===1'b0));
  cover property ($fell(D_N) ##0 (Y===1'b0));

endmodule

// Bind into the DUT to access ports and internal nets
bind sky130_fd_sc_hd__nor4bb sky130_fd_sc_hd__nor4bb_sva nor4bb_sva_i (.*);

`endif