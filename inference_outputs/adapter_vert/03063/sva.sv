property ValidSynceotid; @(posedge aclk) (si_rs_awvalid) |-> S == m_payload_i_reg[47:44] ;endproperty 
 
 property ValidNexteotid; @(posedge aclk) (next) |-> next_pending_r_reg == 1'b1 ;endproperty 
 
 property ValidAddrInceotid; @(posedge aclk) (axaddr_incr) |-> m_axi_awaddr == m_axi_awaddr + axaddr_incr ;endproperty 
 
 property ValidSynceotid; @(posedge aclk) (m_payload_i_reg[39] != m_payload_i_reg_prev[39]) |-> Q == m_payload_i_reg[39:39] ;endproperty 
 
 property SyncStateeotid; @(posedge aclk) (state_reg[1] != state_reg_prev[1]) |-> wrap_second_len_r_reg == state_reg[1:0] ;endproperty 
 
 property SyncNexteotid; @(posedge aclk) (next != next_prev) |-> next_pending_r_reg == next ;endproperty 
 