
module inst_mem(
    input  [6:0] addra,
    output [15:0] douta
);

reg [15:0] mem [127:0]; // Assuming a memory of 128 16-bit words

assign douta = mem[addra];

endmodule

module instruction_fetch(
    input         clk_n,
    input         rst_n,
    input  [6:0]  m_branch_addr,
    input         m_branch_en,
    output [6:0]  if_next_addr,
    output [15:0] if_curr_inst
);

reg [6:0] pc;

assign if_next_addr = pc + 1;

// Added b/c the assign won't work (reg needs always block)
always@(posedge clk_n or negedge rst_n) begin
  if(!rst_n) begin
    pc <= 7'b0;
  end else begin
    if(m_branch_en) begin
      pc <= m_branch_addr;
    end else begin
      pc <= if_next_addr;
    end
  end
end


inst_mem i_inst_mem(
  .addra(pc),
  .douta(if_curr_inst)
);

endmodule
