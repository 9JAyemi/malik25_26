// SVA checker for mi_nios_cpu_nios2_oci_fifo_wrptr_inc
module mi_nios_cpu_nios2_oci_fifo_wrptr_inc_sva (
  input logic        ge2_free,
  input logic        ge3_free,
  input logic [1:0]  input_tm_cnt,
  input logic [3:0]  fifo_wrptr_inc
);
  default clocking cb @(posedge $global_clock); endclocking

  // Optional X/Z checks
  a_no_x_inputs:  assert property (!$isunknown({ge2_free, ge3_free, input_tm_cnt}));
  a_no_x_output:  assert property (!$isunknown(fifo_wrptr_inc));

  // Expected increment (priority-encoded)
  let expected_inc = (ge3_free && (input_tm_cnt == 2'b11)) ? 2'd3 :
                     (ge2_free && (input_tm_cnt >= 2))     ? 2'd2 :
                     (               input_tm_cnt >= 1)     ? 2'd1 : 2'd0;

  // Functional equivalence (and upper bits must be 0)
  a_priority_map: assert property (
    (fifo_wrptr_inc[3:2] == 2'b00) && (fifo_wrptr_inc[1:0] == expected_inc)
  );

  // Sanity: only allowed encodings ever appear
  a_allowed_codes: assert property (fifo_wrptr_inc inside {4'b0000,4'b0001,4'b0010,4'b0011});

  // Functional coverage: exercise each selected path
  c_sel_3: cover property (ge3_free && (input_tm_cnt == 2'b11) &&
                           (fifo_wrptr_inc == 4'b0011));
  c_sel_2: cover property ((input_tm_cnt >= 2) && ge2_free &&
                           !(ge3_free && (input_tm_cnt == 2'b11)) &&
                           (fifo_wrptr_inc == 4'b0010));
  c_sel_1: cover property ((input_tm_cnt >= 1) &&
                           !(ge3_free && (input_tm_cnt == 2'b11)) &&
                           !(ge2_free && (input_tm_cnt >= 2)) &&
                           (fifo_wrptr_inc == 4'b0001));
  c_sel_0: cover property ((input_tm_cnt == 2'd0) &&
                           (fifo_wrptr_inc == 4'b0000));
endmodule

// Bind to the DUT
bind mi_nios_cpu_nios2_oci_fifo_wrptr_inc
  mi_nios_cpu_nios2_oci_fifo_wrptr_inc_sva
  sva_i (.ge2_free(ge2_free),
         .ge3_free(ge3_free),
         .input_tm_cnt(input_tm_cnt),
         .fifo_wrptr_inc(fifo_wrptr_inc));