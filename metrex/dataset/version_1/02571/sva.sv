// SVA for lsu_wb_router (bindable, combinational, concise)
module lsu_wb_router_sva
(
  input [8191:0] in_rd_data,
  input [6:0]    in_wftag_resp,
  input          in_ack,
  input [63:0]   in_exec_value,
  input [11:0]   in_lddst_stsrc_addr,
  input [3:0]    in_reg_wr_en,
  input [31:0]   in_instr_pc,
  input          in_gm_or_lds,

  input [8:0]    out_sgpr_dest_addr,
  input [127:0]  out_sgpr_dest_data,
  input [3:0]    out_sgpr_dest_wr_en,
  input          out_sgpr_instr_done,
  input [5:0]    out_sgpr_instr_done_wfid,

  input [9:0]    out_vgpr_dest_addr,
  input [8191:0] out_vgpr_dest_data,
  input [3:0]    out_vgpr_dest_wr_en,
  input [63:0]   out_vgpr_dest_wr_mask,
  input          out_vgpr_instr_done,
  input [5:0]    out_vgpr_instr_done_wfid,

  input [31:0]   out_tracemon_retire_pc,
  input          out_gm_or_lds,
  input          out_rfa_dest_wr_req
);

  // Combinational immediate assertions and coverage
  always @* begin
    // Pass-through mappings
    assert (out_sgpr_dest_addr       === in_lddst_stsrc_addr[8:0])   else $error("sgpr addr map");
    assert (out_sgpr_dest_data       === in_rd_data[127:0])          else $error("sgpr data map");
    assert (out_sgpr_instr_done_wfid === in_wftag_resp[6:1])         else $error("sgpr wfid map");

    assert (out_vgpr_dest_addr       === in_lddst_stsrc_addr[9:0])   else $error("vgpr addr map");
    assert (out_vgpr_dest_data       === in_rd_data)                 else $error("vgpr data map");
    assert (out_vgpr_dest_wr_mask    === in_exec_value)              else $error("vgpr mask map");
    assert (out_vgpr_instr_done_wfid === in_wftag_resp[6:1])         else $error("vgpr wfid map");

    assert (out_tracemon_retire_pc   === in_instr_pc)                else $error("pc map");
    assert (out_gm_or_lds            === in_gm_or_lds)               else $error("gm/lds map");

    // Aggregate req
    assert (out_rfa_dest_wr_req === ((|out_vgpr_dest_wr_en) | (|out_sgpr_dest_wr_en)))
      else $error("rfa req");

    // Mutual exclusion
    assert (!(out_sgpr_instr_done && out_vgpr_instr_done))
      else $error("both done high");

    // Known control outputs when controlling inputs are known
    if (!$isunknown({in_ack, in_wftag_resp[0], in_lddst_stsrc_addr[11:10], in_reg_wr_en})) begin
      assert (!$isunknown({out_sgpr_dest_wr_en, out_vgpr_dest_wr_en, out_sgpr_instr_done, out_vgpr_instr_done, out_rfa_dest_wr_req}))
        else $error("unknown control outputs");
    end

    // Decode behavior mirrors casex table
    if (!in_ack) begin
      assert (out_sgpr_dest_wr_en==4'b0 && out_vgpr_dest_wr_en==4'b0 &&
              out_sgpr_instr_done==1'b0 && out_vgpr_instr_done==1'b0)
        else $error("ack0 idle");
    end else if (in_lddst_stsrc_addr[11]==1'b0) begin
      assert (out_sgpr_dest_wr_en==4'b0 && out_vgpr_dest_wr_en==4'b0 &&
              out_sgpr_instr_done==1'b0 && out_vgpr_instr_done==1'b0)
        else $error("addr[11]==0 idle");
    end else if (in_lddst_stsrc_addr[11:10]==2'b10) begin
      assert (out_sgpr_dest_wr_en==4'b0 && out_sgpr_instr_done==1'b0 && out_vgpr_instr_done==1'b1)
        else $error("vgpr done shape");
      if (in_wftag_resp[0]) assert (out_vgpr_dest_wr_en==in_reg_wr_en) else $error("vgpr wr_en when wftag1");
      else                  assert (out_vgpr_dest_wr_en==4'b0)         else $error("vgpr wr_en when wftag0");
    end else begin // 2'b11
      assert (out_vgpr_dest_wr_en==4'b0 && out_vgpr_instr_done==1'b0 && out_sgpr_instr_done==1'b1)
        else $error("sgpr done shape");
      if (in_wftag_resp[0]) assert (out_sgpr_dest_wr_en==in_reg_wr_en) else $error("sgpr wr_en when wftag1");
      else                  assert (out_sgpr_dest_wr_en==4'b0)         else $error("sgpr wr_en when wftag0");
    end

    // Output->input implications
    if (out_vgpr_instr_done) assert (in_ack && in_lddst_stsrc_addr[11:10]==2'b10) else $error("vgpr done implies sel");
    if (out_sgpr_instr_done) assert (in_ack && in_lddst_stsrc_addr[11:10]==2'b11) else $error("sgpr done implies sel");

    // Coverage of all decode arms and req kinds
    cover (!in_ack);
    cover (in_ack && in_lddst_stsrc_addr[11]==1'b0);
    cover (in_ack && in_lddst_stsrc_addr[11:10]==2'b10 &&  in_wftag_resp[0]);
    cover (in_ack && in_lddst_stsrc_addr[11:10]==2'b10 && !in_wftag_resp[0]);
    cover (in_ack && in_lddst_stsrc_addr[11:10]==2'b11 &&  in_wftag_resp[0]);
    cover (in_ack && in_lddst_stsrc_addr[11:10]==2'b11 && !in_wftag_resp[0]);
    cover (out_rfa_dest_wr_req &&  |out_vgpr_dest_wr_en && !|out_sgpr_dest_wr_en);
    cover (out_rfa_dest_wr_req && !|out_vgpr_dest_wr_en &&  |out_sgpr_dest_wr_en);
  end
endmodule

bind lsu_wb_router lsu_wb_router_sva
(
  .in_rd_data(in_rd_data),
  .in_wftag_resp(in_wftag_resp),
  .in_ack(in_ack),
  .in_exec_value(in_exec_value),
  .in_lddst_stsrc_addr(in_lddst_stsrc_addr),
  .in_reg_wr_en(in_reg_wr_en),
  .in_instr_pc(in_instr_pc),
  .in_gm_or_lds(in_gm_or_lds),

  .out_sgpr_dest_addr(out_sgpr_dest_addr),
  .out_sgpr_dest_data(out_sgpr_dest_data),
  .out_sgpr_dest_wr_en(out_sgpr_dest_wr_en),
  .out_sgpr_instr_done(out_sgpr_instr_done),
  .out_sgpr_instr_done_wfid(out_sgpr_instr_done_wfid),

  .out_vgpr_dest_addr(out_vgpr_dest_addr),
  .out_vgpr_dest_data(out_vgpr_dest_data),
  .out_vgpr_dest_wr_en(out_vgpr_dest_wr_en),
  .out_vgpr_dest_wr_mask(out_vgpr_dest_wr_mask),
  .out_vgpr_instr_done(out_vgpr_instr_done),
  .out_vgpr_instr_done_wfid(out_vgpr_instr_done_wfid),

  .out_tracemon_retire_pc(out_tracemon_retire_pc),
  .out_gm_or_lds(out_gm_or_lds),
  .out_rfa_dest_wr_req(out_rfa_dest_wr_req)
);