// SVA for instruction_fetch and inst_mem

// Assertions bound into instruction_fetch
module if_sva #(parameter ADDR_W=7, INST_W=16) (
  input  logic                   clk_n,
  input  logic                   rst_n,
  input  logic [ADDR_W-1:0]      pc,
  input  logic [ADDR_W-1:0]      m_branch_addr,
  input  logic                   m_branch_en,
  input  logic [ADDR_W-1:0]      if_next_addr,
  input  logic [INST_W-1:0]      if_curr_inst
);
  default clocking cb @(posedge clk_n); endclocking

  // Basic sanity / X-checks
  assert property ( !$isunknown(m_branch_en) );
  assert property ( m_branch_en |-> !$isunknown(m_branch_addr) );
  assert property ( if_next_addr == pc + 1'b1 );
  assert property ( !rst_n |-> pc == '0 );
  assert property ( disable iff (!rst_n) !$isunknown(pc) );
  assert property ( disable iff (!rst_n) !$isunknown(if_next_addr) );

  // Sequential PC behavior
  assert property ( disable iff (!rst_n)
                    !m_branch_en |=> pc == $past(pc) + 1'b1 );

  assert property ( disable iff (!rst_n)
                    m_branch_en |=> pc == $past(m_branch_addr) );

  // Instruction read should be stable if address is stable (read-only mem)
  assert property ( disable iff (!rst_n)
                    $stable(pc) |=> $stable(if_curr_inst) );

  // Coverage
  cover property ( !rst_n ##1 rst_n ); // reset pulse
  cover property ( disable iff (!rst_n) (!m_branch_en)[*3] ); // straight-line fetch
  cover property ( disable iff (!rst_n) m_branch_en ); // any branch
  cover property ( disable iff (!rst_n)
                   (pc == {ADDR_W{1'b1}} && !m_branch_en) ##1 pc == '0 ); // wrap
  cover property ( disable iff (!rst_n)
                   (m_branch_en && m_branch_addr == '0) ##1 pc == '0 ); // branch to 0
  cover property ( disable iff (!rst_n)
                   (m_branch_en && m_branch_addr == {ADDR_W{1'b1}}) ##1 pc == {ADDR_W{1'b1}} ); // branch to max
endmodule

// Assertions bound into inst_mem (purely combinational read)
module imem_sva #(parameter ADDR_W=7, INST_W=16) (
  input  logic [ADDR_W-1:0]                 addra,
  input  logic [INST_W-1:0]                 douta,
  input  logic [INST_W-1:0]                 mem [0:(1<<ADDR_W)-1]
);
  // Combinational mapping must always hold
  assert property ( douta == mem[addra] );

  // Address should not be X/Z
  assert property ( !$isunknown(addra) );

  // Simple address corner coverage
  cover property ( addra == '0 );
  cover property ( addra == {ADDR_W{1'b1}} );
endmodule

// Bind SVA to DUTs
bind instruction_fetch if_sva #(.ADDR_W(7), .INST_W(16)) u_if_sva (
  .clk_n(clk_n),
  .rst_n(rst_n),
  .pc(pc),
  .m_branch_addr(m_branch_addr),
  .m_branch_en(m_branch_en),
  .if_next_addr(if_next_addr),
  .if_curr_inst(if_curr_inst)
);

bind inst_mem imem_sva #(.ADDR_W(7), .INST_W(16)) u_imem_sva (
  .addra(addra),
  .douta(douta),
  .mem(mem)
);