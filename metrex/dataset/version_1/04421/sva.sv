// SVA for sky130_fd_sc_ls__einvn (notif0: Z = ~A when TE_B==0, else Z = Z)
module sky130_fd_sc_ls__einvn_sva (input wire Z, A, TE_B);

  // Functional correctness
  assert property (@(A or TE_B)
    (TE_B === 1'b0 && (A === 1'b0 || A === 1'b1)) |-> (Z === ~A)
  ) else $error("einvn: TE_B=0 requires Z=~A");

  assert property (@(A or TE_B or Z)
    (TE_B === 1'b1) |-> (Z === 1'bz)
  ) else $error("einvn: TE_B=1 requires Z=Z");

  // Input/X-discipline
  assert property (@(TE_B)
    !$isunknown(TE_B)
  ) else $error("einvn: TE_B must be 0/1, not X/Z");

  assert property (@(A or TE_B)
    (TE_B === 1'b0) |-> !$isunknown(A)
  ) else $error("einvn: A must be known when enabled");

  // Driven/not-driven guarantees
  assert property (@(A or TE_B or Z)
    (TE_B === 1'b0) |-> (Z !== 1'bz && !$isunknown(Z))
  ) else $error("einvn: Z must be 0/1 when enabled");

  assert property (@(A or TE_B or Z)
    (TE_B === 1'b1 && $changed(A)) |-> (Z === 1'bz)
  ) else $error("einvn: Z must remain Z while tri-stated");

  // Coverage
  cover property (@(A or TE_B or Z)
    (TE_B===1'b1 && Z===1'bz)
  );

  cover property (@(A or TE_B)
    (TE_B===1'b0 && A===1'b0 && Z===1'b1) ##1 (A===1'b1 && Z===1'b0)
  );

  cover property (@(A or TE_B)
    (TE_B===1'b0 && A===1'b1 && Z===1'b0) ##1 (A===1'b0 && Z===1'b1)
  );

  cover property (@(A or TE_B)
    (TE_B===1'b0 && (A inside {0,1}) && Z===~A) ##1 (TE_B===1'b1 && Z===1'bz)
  );

  cover property (@(A or TE_B)
    (TE_B===1'b1 && Z===1'bz) ##1 (TE_B===1'b0 && (A inside {0,1}) && Z===~A)
  );

endmodule

bind sky130_fd_sc_ls__einvn sky130_fd_sc_ls__einvn_sva sva_inst (.*);