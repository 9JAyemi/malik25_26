// SVA for sky130_fd_sc_hd__mux_2
module sky130_fd_sc_hd__mux_2_sva #(parameter W=4)
(
  input  logic [W-1:0] A,
  input  logic [W-1:0] B,
  input  logic         S,
  input  logic [W-1:0] Y
);

  // Combinational equivalence (delta-cycle safe)
  always_comb
    assert #0 (Y === (S ? B : A))
      else $error("MUX func mismatch: Y != (S?B:A)");

  // If all inputs are known, output must be known
  assert property (@(A or B or S)
                   (!$isunknown({S,A,B})) |-> !$isunknown(Y))
    else $error("MUX X-prop: known inputs produced unknown Y");

  // Functional path coverage: observe meaningful selection on S edges
  cover property (@(posedge S) (A !== B) && (Y === B));
  cover property (@(negedge S) (A !== B) && (Y === A));

  // Data-path propagation coverage when selected input changes
  cover property (@(A) (S === 1'b0 && $changed(A) && (A !== B)) ##0 (Y === A));
  cover property (@(B) (S === 1'b1 && $changed(B) && (A !== B)) ##0 (Y === B));

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__mux_2 sky130_fd_sc_hd__mux_2_sva #(.W(4)) mux2_sva_i (.*);