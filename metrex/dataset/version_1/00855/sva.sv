// SVA checker for NIOS_Sys_nios2_qsys_0_nios2_oci_fifocount_inc
module nios2_oci_fifocount_inc_sva (
  input logic clk,
  input logic rst_n,
  input logic empty,
  input logic free2,
  input logic free3,
  input logic [1:0] tm_count,
  input logic [4:0] fifocount_inc
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n || $isunknown({empty,free2,free3,tm_count}));

  function automatic logic [4:0] inc_ref(
    input logic empty_i,
    input logic free2_i,
    input logic free3_i,
    input logic [1:0] tm_count_i
  );
    if (empty_i)                         inc_ref = {3'b000, tm_count_i};
    else if (free3_i && (tm_count_i==3)) inc_ref = 5'd2;
    else if (free2_i && (tm_count_i>=2)) inc_ref = 5'd1;
    else if (tm_count_i>=1)              inc_ref = 5'd0;
    else                                 inc_ref = 5'd31;
  endfunction

  // Functional equivalence (golden reference)
  assert property (fifocount_inc == inc_ref(empty, free2, free3, tm_count));

  // No X on output when inputs are known
  assert property ( !$isunknown({empty,free2,free3,tm_count}) |-> !$isunknown(fifocount_inc) );

  // Coverage: hit each priority branch and result
  cover property ( empty && (fifocount_inc == {3'b000, tm_count}) );
  cover property ( !empty && free3 && (tm_count==2'b11) && (fifocount_inc==5'd2) );
  cover property ( !empty && !(free3 && tm_count==2'b11) && free2 && (tm_count>=2) && (fifocount_inc==5'd1) );
  cover property ( !empty && !(free3 && tm_count==2'b11) && !(free2 && (tm_count>=2)) && (tm_count>=1) && (fifocount_inc==5'd0) );
  cover property ( !empty && (tm_count==2'b00) && (fifocount_inc==5'd31) );

endmodule

// Example bind (connect clk/rst from your TB/top)
bind NIOS_Sys_nios2_qsys_0_nios2_oci_fifocount_inc nios2_oci_fifocount_inc_sva u_fifocount_inc_sva (
  .clk(tb_clk),
  .rst_n(tb_rst_n),
  .empty(empty),
  .free2(free2),
  .free3(free3),
  .tm_count(tm_count),
  .fifocount_inc(fifocount_inc)
);