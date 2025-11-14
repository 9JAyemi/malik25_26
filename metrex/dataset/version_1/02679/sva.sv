// SVA checker for sky130_fd_sc_ls__nand4
module nand4_sva (input logic A, B, C, D, Y);

  // Functional correctness for known inputs (4-state clean)
  // On any input change, in the same timestep after settling, Y must be NAND(A,B,C,D)
  assert property (@(A or B or C or D or Y)
                   (!$isunknown({A,B,C,D})) |-> ##0 (Y === ~(A & B & C & D)))
    else $error("NAND4 truth failure for known inputs");

  // Strong 4-state semantics of primitive nand:
  // Any controlling 0 forces Y=1
  assert property (@(A or B or C or D or Y)
                   ((A===1'b0)||(B===1'b0)||(C===1'b0)||(D===1'b0)) |-> ##0 (Y===1'b1))
    else $error("NAND4 did not drive 1 with a controlling 0");

  // All 1's force Y=0
  assert property (@(A or B or C or D or Y)
                   ((A===1'b1)&&(B===1'b1)&&(C===1'b1)&&(D===1'b1)) |-> ##0 (Y===1'b0))
    else $error("NAND4 did not drive 0 with all ones");

  // If no input is 0 and not all are 1 (i.e., some X/Z present), Y must be X
  assert property (@(A or B or C or D or Y)
                   (((A!==1'b0)&&(B!==1'b0)&&(C!==1'b0)&&(D!==1'b0)) &&
                    ((A!==1'b1)||(B!==1'b1)||(C!==1'b1)||(D!==1'b1))) |-> ##0 (Y===1'bx))
    else $error("NAND4 X-propagation semantics violated");

  // Minimal toggling coverage on Y
  cover property (@(Y) $rose(Y));
  cover property (@(Y) $fell(Y));

  // Functional coverage: hit all 16 input combinations
  // (Uses 4-state match; X/Z will not satisfy these covers)
  genvar i;
  for (i = 0; i < 16; i++) begin : cov_inputs
    localparam logic [3:0] V = i[3:0];
    cover property (@(A or B or C or D) ##0 ({A,B,C,D} === V));
  end

  // Cover an X-propagation scenario (no 0s, not all 1s, so some X/Z) leading to Y==X
  cover property (@(A or B or C or D or Y)
                  (((A!==1'b0)&&(B!==1'b0)&&(C!==1'b0)&&(D!==1'b0)) &&
                   ((A!==1'b1)||(B!==1'b1)||(C!==1'b1)||(D!==1'b1))) ##0 (Y===1'bx));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__nand4 nand4_sva u_nand4_sva (.*);