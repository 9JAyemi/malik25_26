// SVA for amm_master_qsys_with_pcie_sgdma_command_grabber
// Bind into DUT; concise, high-value checks and coverage

module amm_master_qsys_with_pcie_sgdma_command_grabber_sva_bind();

  // Default clocking/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Reset behavior (checked during reset)
  assert property (@(posedge clk)
    !reset_n |-> (read_command_data==0 && write_command_data==0 &&
                  command_fifo_rdreq==0 && read_command_valid==0 &&
                  write_command_valid==0 && delay1_command_valid==0 &&
                  command_valid==0));

  // Data formation (registered one cycle after inputs)
  assert property (@cb $past(reset_n) |->
    read_command_data ==
      {$past(write_fixed_address),
       $past(generate_eop),
       ~($past(read_fixed_address)),
       $past(read_burst),
       $past(bytes_to_transfer),
       $past(read_address)});

  assert property (@cb $past(reset_n) |->
    write_command_data ==
      {~($past(write_fixed_address)),
       $past(write_burst),
       $past(bytes_to_transfer),
       $past(write_address)});

  // Valid mirroring
  assert property (@cb read_command_valid == command_valid);
  assert property (@cb write_command_valid == command_valid);

  // Pipeline relationships
  assert property (@cb $past(reset_n) |-> delay1_command_valid == $past(command_fifo_rdreq));
  assert property (@cb $past(reset_n) |-> command_valid        == $past(delay1_command_valid));
  assert property (@cb $past(reset_n,2) |-> command_valid == $past(command_fifo_rdreq,2));

  // Rdreq combinational in calculation
  assert property (@cb
    command_fifo_rdreq_in ==
      ((command_fifo_rdreq || command_valid) ? 1'b0
         : (~read_go && ~write_go && ~m_read_waitrequest && ~m_write_waitrequest)));

  // Rdreq register update semantics w.r.t. FIFO empty
  assert property (@cb $past(reset_n) && $past(!command_fifo_empty)
                   |-> command_fifo_rdreq == $past(command_fifo_rdreq_in));
  assert property (@cb $past(reset_n) && $past(command_fifo_empty)
                   |-> command_fifo_rdreq == $past(command_fifo_rdreq));

  // Rdreq rise implies prior gating satisfied and FIFO not empty
  assert property (@cb $rose(command_fifo_rdreq) |->
    $past(!command_fifo_empty &&
          !command_valid &&
          !read_go && !write_go &&
          !m_read_waitrequest && !m_write_waitrequest));

  // Rdreq and command_valid are never high together
  assert property (@cb !(command_fifo_rdreq && command_valid));

  // Basic functional coverage
  cover property (@cb $rose(command_fifo_rdreq));
  cover property (@cb command_fifo_rdreq ##2 command_valid);
  cover property (@cb generate_eop && command_fifo_rdreq);
  cover property (@cb read_fixed_address==0 && write_fixed_address==0 && command_fifo_rdreq);
  cover property (@cb read_fixed_address==1 && write_fixed_address==1 && command_fifo_rdreq);
  cover property (@cb atlantic_channel==4'h0 && command_fifo_rdreq);
  cover property (@cb atlantic_channel==4'hF && command_fifo_rdreq);
  cover property (@cb read_burst==8'h00  && command_fifo_rdreq);
  cover property (@cb read_burst==8'hFF  && command_fifo_rdreq);
  cover property (@cb bytes_to_transfer==16'h0000 && command_fifo_rdreq);
  cover property (@cb bytes_to_transfer==16'hFFFF && command_fifo_rdreq);

endmodule

bind amm_master_qsys_with_pcie_sgdma_command_grabber
     amm_master_qsys_with_pcie_sgdma_command_grabber_sva_bind sva_check();