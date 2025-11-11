// SVA checker for wishbone_mem_interconnect
module wishbone_mem_interconnect_sva #(
  parameter MEM_SEL_0    = 0,
  parameter MEM_OFFSET_0 = 32'h00000000,
  parameter MEM_SIZE_0   = 32'h0080_0000
)(
  input  logic         clk,
  input  logic         rst,

  input  logic         i_m_we,
  input  logic         i_m_stb,
  input  logic         i_m_cyc,
  input  logic [3:0]   i_m_sel,
  input  logic [31:0]  i_m_adr,
  input  logic [31:0]  i_m_dat,
  input  logic [31:0]  o_m_dat,
  input  logic         o_m_ack,
  input  logic         o_m_int,

  input  logic         o_s0_we,
  input  logic         o_s0_cyc,
  input  logic         o_s0_stb,
  input  logic [3:0]   o_s0_sel,
  input  logic         i_s0_ack,
  input  logic [31:0]  o_s0_dat,
  input  logic [31:0]  i_s0_dat,
  input  logic [31:0]  o_s0_adr,
  input  logic         i_s0_int
);

  // Param sanity
  initial begin
    assert (MEM_SIZE_0 != 32'h0) else $error("MEM_SIZE_0 must be non-zero");
  end

  function automatic bit in_range_f (logic [31:0] adr);
    return (!rst) && (adr >= MEM_OFFSET_0) && (adr < (MEM_OFFSET_0 + MEM_SIZE_0));
  endfunction

  let in_range = in_range_f(i_m_adr);

  // Decode to slave: when in-range, pass-through; else drive zeros
  assert property (@(posedge clk) disable iff (rst)
    in_range |-> (o_s0_we==i_m_we && o_s0_stb==i_m_stb && o_s0_cyc==i_m_cyc &&
                  o_s0_sel==i_m_sel && o_s0_adr==i_m_adr && o_s0_dat==i_m_dat))
    else $error("Decode to s0 mismatch when in-range");

  assert property (@(posedge clk) disable iff (rst)
    !in_range |-> (o_s0_we==1'b0 && o_s0_stb==1'b0 && o_s0_cyc==1'b0 &&
                   o_s0_sel==4'h0 && o_s0_adr==32'h0 && o_s0_dat==32'h0))
    else $error("s0 not forced low when out-of-range");

  // Master return signals: pass-through vs zeros
  assert property (@(posedge clk) disable iff (rst)
    in_range |-> (o_m_ack==i_s0_ack && o_m_int==i_s0_int && o_m_dat==i_s0_dat))
    else $error("Master return mismatch when in-range");

  assert property (@(posedge clk) disable iff (rst)
    !in_range |-> (o_m_ack==1'b0 && o_m_int==1'b0 && o_m_dat==32'h0))
    else $error("Master return not zeroed when out-of-range");

  // No spurious ACK/INT when not selected; bidirectional implications
  assert property (@(posedge clk) disable iff (rst)
    (i_s0_ack && in_range) |-> o_m_ack)
    else $error("ACK not propagated to master");

  assert property (@(posedge clk) disable iff (rst)
    o_m_ack |-> (i_s0_ack && in_range))
    else $error("Spurious master ACK");

  assert property (@(posedge clk) disable iff (rst)
    (i_s0_int && in_range) |-> o_m_int)
    else $error("INT not propagated to master");

  assert property (@(posedge clk) disable iff (rst)
    o_m_int |-> (i_s0_int && in_range))
    else $error("Spurious master INT");

  // Out-of-range access must not produce ACK
  assert property (@(posedge clk) disable iff (rst)
    (!in_range && i_m_cyc && i_m_stb) |-> !o_m_ack)
    else $error("ACK seen for out-of-range access");

  // No X on outputs after reset deassert
  assert property (@(posedge clk) disable iff (rst)
    !$isunknown({o_s0_we,o_s0_stb,o_s0_cyc,o_s0_sel,o_s0_adr,o_s0_dat,
                 o_m_dat,o_m_ack,o_m_int}))
    else $error("Unknowns on outputs");

  // Coverage: read, write, OOR, boundaries, and interrupt
  cover property (@(posedge clk) disable iff (rst)
    in_range && i_m_cyc && i_m_stb && !i_m_we ##1 i_s0_ack);

  cover property (@(posedge clk) disable iff (rst)
    in_range && i_m_cyc && i_m_stb &&  i_m_we ##1 i_s0_ack);

  cover property (@(posedge clk) disable iff (rst)
    !in_range && i_m_cyc && i_m_stb ##1 !o_m_ack[*3]);

  cover property (@(posedge clk) disable iff (rst)
    in_range && i_s0_int);

  cover property (@(posedge clk) disable iff (rst)
    (i_m_adr == MEM_OFFSET_0) && in_range);

  cover property (@(posedge clk) disable iff (rst)
    (i_m_adr == (MEM_OFFSET_0 + MEM_SIZE_0 - 1)) && in_range);

  cover property (@(posedge clk) disable iff (rst)
    (i_m_adr == (MEM_OFFSET_0 + MEM_SIZE_0)) && !in_range);

endmodule

// Bind into DUT (tools supporting bind)
bind wishbone_mem_interconnect wishbone_mem_interconnect_sva #(
  .MEM_SEL_0(MEM_SEL_0),
  .MEM_OFFSET_0(MEM_OFFSET_0),
  .MEM_SIZE_0(MEM_SIZE_0)
) wishbone_mem_interconnect_sva_i (.*);