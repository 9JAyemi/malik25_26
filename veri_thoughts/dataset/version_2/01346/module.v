
module axi_to_custom_protocol_converter
  (output reg next_pending_r_reg,
   output reg [11:0] m_axi_awaddr,
   output reg [47:0] m_payload_i_reg,
   output reg incr_next_pending,
   output reg wrap_next_pending,
   output reg sel_first_reg_0,
   input aclk,
   input [11:0] m_axi_awaddr_in,
   input [47:0] m_payload_i_reg_in,
   input next,
   input incr_next_pending_in,
   input wrap_next_pending_in,
   input sel_first_i);

  always @(posedge aclk) begin
    if (sel_first_i) begin
      m_axi_awaddr <= m_axi_awaddr_in;
      m_payload_i_reg <= m_payload_i_reg_in;
      sel_first_reg_0 <= 1'b1;
      next_pending_r_reg <= 1'b0;
    end else begin
      if (incr_next_pending_in) begin
        m_axi_awaddr <= m_axi_awaddr + 1;
        next_pending_r_reg <= 1'b0;
        incr_next_pending <= 1'b1;
        wrap_next_pending <= 1'b0;
      end else if (wrap_next_pending_in) begin
        m_axi_awaddr <= m_axi_awaddr_in;
        incr_next_pending <= 1'b0;
        wrap_next_pending <= 1'b1;
        next_pending_r_reg <= 1'b0;
      end else if (next) begin
        next_pending_r_reg <= 1'b0;
        incr_next_pending <= 1'b0;
        wrap_next_pending <= 1'b0;
      end
      sel_first_reg_0 <= 1'b0;
    end
  end
endmodule