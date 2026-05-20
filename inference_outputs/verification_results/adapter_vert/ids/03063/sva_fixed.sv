module simplified_axi_protocol_converter_sva (
    input logic Q,
    input logic S,
    input logic aclk,
    input logic axaddr_incr,
    input logic m_axi_awaddr,
    input logic m_payload_i_reg,
    input logic m_payload_i_reg_prev,
    input logic next,
    input logic next_pending_r_reg,
    input logic next_prev,
    input logic si_rs_awvalid,
    input logic state_reg,
    input logic state_reg_prev,
    input logic wrap_second_len_r_reg,
    input logic b1
);

property ValidSynceotid; @(posedge aclk) (si_rs_awvalid) |-> S == m_payload_i_reg[47:44] ;endproperty
assert property (ValidSynceotid);

property ValidNexteotid; @(posedge aclk) (next) |-> next_pending_r_reg == 1'b1 ;endproperty
assert property (ValidNexteotid);

property ValidAddrInceotid; @(posedge aclk) (axaddr_incr) |-> m_axi_awaddr == m_axi_awaddr + axaddr_incr ;endproperty
assert property (ValidAddrInceotid);

property ValidSynceotid_2; @(posedge aclk) (m_payload_i_reg[39] != m_payload_i_reg_prev[39]) |-> Q == m_payload_i_reg[39:39] ;endproperty
assert property (ValidSynceotid_2);

property SyncStateeotid; @(posedge aclk) (state_reg[1] != state_reg_prev[1]) |-> wrap_second_len_r_reg == state_reg[1:0] ;endproperty
assert property (SyncStateeotid);

property SyncNexteotid; @(posedge aclk) (next != next_prev) |-> next_pending_r_reg == next ;endproperty
assert property (SyncNexteotid);

endmodule