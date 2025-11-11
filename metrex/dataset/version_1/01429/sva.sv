// SVA for processing_system7_v5_3_aw_atc
// Bind this module to the DUT definition
// bind processing_system7_v5_3_aw_atc processing_system7_v5_3_aw_atc_sva sva();

module processing_system7_v5_3_aw_atc_sva;

  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // Reset behavior
  assert property (ARESET |=> addr_ptr == {C_FIFO_DEPTH_LOG{1'b1}});
  assert property (ARESET |=> !cmd_full && !cmd_w_valid);

  // Gating and push definition
  assert property (M_AXI_AWVALID == (S_AXI_AWVALID && !cmd_full));
  assert property (S_AXI_AWREADY == (M_AXI_AWREADY && !cmd_full));
  assert property (cmd_w_push == (S_AXI_AWVALID && M_AXI_AWREADY && !cmd_full));
  assert property (cmd_full |-> !S_AXI_AWREADY && !M_AXI_AWVALID);

  // Pass-through of AW channel payloads
  assert property (M_AXI_AWID    == S_AXI_AWID);
  assert property (M_AXI_AWADDR  == S_AXI_AWADDR);
  assert property (M_AXI_AWLEN   == S_AXI_AWLEN);
  assert property (M_AXI_AWSIZE  == S_AXI_AWSIZE);
  assert property (M_AXI_AWBURST == S_AXI_AWBURST);
  assert property (M_AXI_AWLOCK  == S_AXI_AWLOCK);
  assert property (M_AXI_AWCACHE == S_AXI_AWCACHE);
  assert property (M_AXI_AWPROT  == S_AXI_AWPROT);
  assert property (M_AXI_AWUSER  == S_AXI_AWUSER);

  // Pointer arithmetic
  assert property (( cmd_w_push && !cmd_w_ready) |=> addr_ptr == $past(addr_ptr)+1);
  assert property ((!cmd_w_push &&  cmd_w_ready) |=> addr_ptr == $past(addr_ptr)-1);
  assert property (((cmd_w_push &&  cmd_w_ready) ||
                    (!cmd_w_push && !cmd_w_ready)) |=> addr_ptr == $past(addr_ptr));

  // all_addr_ptr computation and cmd_full update policy
  assert property (all_addr_ptr == (addr_ptr + cmd_b_addr + 2));
  assert property (( cmd_w_push && !cmd_b_ready) |=> cmd_full == (all_addr_ptr == C_FIFO_DEPTH-3));
  assert property ((!cmd_w_push &&  cmd_b_ready) |=> cmd_full == (all_addr_ptr == C_FIFO_DEPTH-2));
  assert property (((cmd_w_push &&  cmd_b_ready) ||
                    (!cmd_w_push && !cmd_b_ready)) |=> cmd_full == $past(cmd_full));

  // cmd_w_valid update policy
  assert property (( cmd_w_push && !cmd_w_ready) |=> cmd_w_valid);
  assert property ((!cmd_w_push &&  cmd_w_ready) |=> cmd_w_valid == ($past(addr_ptr) != 0));
  assert property (((cmd_w_push &&  cmd_w_ready) ||
                    (!cmd_w_push && !cmd_w_ready)) |=> cmd_w_valid == $past(cmd_w_valid));

  // SRL data path behavior
  genvar i;
  generate
    for (i = 0; i < C_FIFO_DEPTH-1; i++) begin : g_shift
      if (i < C_FIFO_DEPTH-1) begin
        assert property (cmd_w_push |=> data_srl[i+1] == $past(data_srl[i]));
      end
    end
  endgenerate
  assert property (cmd_w_push |=> data_srl[0] == {access_is_optimized, S_AXI_AWID});

  // Read-out mapping
  assert property ({cmd_w_check, cmd_w_id} == data_srl[addr_ptr]);

  // Optimized access classification equivalences
  assert property (access_is_incr  == (S_AXI_AWBURST == C_INCR_BURST));
  assert property (access_is_wrap  == (S_AXI_AWBURST == C_WRAP_BURST));
  assert property (access_is_coherent == (S_AXI_AWUSER[0] && S_AXI_AWCACHE[1]));
  assert property (incr_addr_boundary == (S_AXI_AWADDR[4:0] == C_NO_ADDR_OFFSET));
  assert property (access_optimized_size == (S_AXI_AWSIZE == C_OPTIMIZED_SIZE) && (S_AXI_AWLEN == C_OPTIMIZED_LEN));
  assert property (incr_is_optimized == (access_is_incr && access_is_coherent && access_optimized_size && incr_addr_boundary));
  assert property (wrap_is_optimized == (access_is_wrap && access_is_coherent && access_optimized_size));
  assert property (access_is_optimized == (incr_is_optimized || wrap_is_optimized));

  // X-propagation guards (no X/Z on key outputs when not in reset)
  assert property (!$isunknown({cmd_w_valid, cmd_w_check, cmd_w_id}));
  assert property (!$isunknown({S_AXI_AWREADY, M_AXI_AWVALID}));
  assert property (!$isunknown({M_AXI_AWID, M_AXI_AWADDR, M_AXI_AWLEN, M_AXI_AWSIZE,
                                M_AXI_AWBURST, M_AXI_AWLOCK, M_AXI_AWCACHE, M_AXI_AWPROT, M_AXI_AWUSER}));

  // Functional coverage
  cover property (cmd_w_push);                                // AW transfer
  cover property (!cmd_w_push && cmd_w_ready);                // pop-only
  cover property (cmd_w_push && cmd_w_ready);                 // push and pop same cycle
  cover property (all_addr_ptr == C_FIFO_DEPTH-3 && cmd_w_push && !cmd_b_ready);
  cover property (all_addr_ptr == C_FIFO_DEPTH-2 && !cmd_w_push && cmd_b_ready);
  cover property (cmd_full ##1 !cmd_full);                    // full then not full

  cover property (cmd_w_push && (S_AXI_AWBURST == C_INCR_BURST));
  cover property (cmd_w_push && (S_AXI_AWBURST == C_WRAP_BURST));
  cover property (cmd_w_push && access_is_optimized);
  cover property (cmd_w_push && !access_is_optimized);

endmodule