// SVA for db_qp
module db_qp_sva (
  input logic clk,
  input logic rst_n,
  input logic cbf_4x4_i,
  input logic cbf_u_4x4_i,
  input logic cbf_v_4x4_i,
  input logic qp_left_i,
  input logic qp_flag_o
);

  // Local recompute of modified_flag
  let modified_flag = !(cbf_4x4_i || cbf_u_4x4_i || cbf_v_4x4_i);

  // Check async reset effect at clock edge (not disabled)
  assert property (@(posedge clk) (!rst_n) |-> (qp_flag_o == 1'b0))
    else $error("qp_flag_o not 0 during reset");

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // On modified_flag, output captures qp_left_i next cycle
  assert property (modified_flag |=> (qp_flag_o == $past(qp_left_i)))
    else $error("qp_flag_o did not follow qp_left_i when modified_flag=1");

  // When not modified_flag, output forced to 0 next cycle
  assert property (!modified_flag |=> (qp_flag_o == 1'b0))
    else $error("qp_flag_o not 0 when modified_flag=0");

  // Safety: output high only if allowed by prior cycle conditions
  assert property (qp_flag_o |-> $past(modified_flag && qp_left_i))
    else $error("qp_flag_o asserted without prior modified_flag && qp_left_i");

  // No X/Z on output after reset deasserted
  assert property (!$isunknown(qp_flag_o))
    else $error("qp_flag_o is X/Z");

  // Coverage
  cover property (modified_flag && qp_left_i ##1 qp_flag_o)
    ; // took the 'capture 1' branch

  cover property (!modified_flag ##1 qp_flag_o == 1'b0)
    ; // took the 'force 0' branch

  cover property (!modified_flag ##1 modified_flag && qp_left_i ##1 qp_flag_o)
    ; // transition from force-0 branch to capture-1

  cover property ($rose(rst_n) ##1 modified_flag && qp_left_i ##1 qp_flag_o)
    ; // after reset release, capture occurs

endmodule

// Bind into DUT
bind db_qp db_qp_sva db_qp_sva_i (.*);