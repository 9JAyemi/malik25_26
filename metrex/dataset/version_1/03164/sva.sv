// SVA for axi_arbiter
// Bind into the DUT to access internal state/temp_state/params
bind axi_arbiter axi_arbiter_sva sva();

module axi_arbiter_sva;
  // Use DUT scope via bind (all signals/params are visible here)
  default clocking cb @(posedge sw_clk); endclocking
  default disable iff (!rstn)

  // ----------------------------------------
  // Reset and state-encoding hygiene
  // ----------------------------------------
  // After reset release, go to wait_req and outputs cleared
  assert property ($rose(rstn) |-> state == wait_req && prt_req == 0 && prt_ack1 == 0 && prt_ack2 == 0 && prt_qos == 3'b0);

  // State must always be a legal encoding
  assert property (state == wait_req || state == serv_req1 || state == serv_req2 || state == wait_ack_low);

  // wait_ack_low is a one-cycle parking state back to wait_req
  assert property (state == wait_ack_low |=> state == wait_req);

  // No simultaneous acks
  assert property (!(prt_ack1 && prt_ack2));

  // In serv_req1, ack2 must be low; in serv_req2, ack1 must be low
  assert property ((state == serv_req1) |-> prt_ack2 == 0);
  assert property ((state == serv_req2) |-> prt_ack1 == 0);

  // When ack is asserted in service, prt_req must be deasserted same cycle
  assert property ((state == serv_req1 && prt_ack1) |-> !prt_req);
  assert property ((state == serv_req2 && prt_ack2) |-> !prt_req);

  // temp_state must capture the just-serviced state when moving to wait_ack_low
  assert property ((state == wait_ack_low && $past(state) == serv_req1) |-> temp_state == serv_req1);
  assert property ((state == wait_ack_low && $past(state) == serv_req2) |-> temp_state == serv_req2);

  // ----------------------------------------
  // Request selection from wait_req
  // ----------------------------------------
  // Single requester: choose that requester and copy its payload
  assert property (state == wait_req && prt_dv1 && !prt_dv2 |=> state == serv_req1 && prt_req &&
                   prt_qos  == $past(qos1)  &&
                   prt_data == $past(prt_data1) &&
                   prt_addr == $past(prt_addr1) &&
                   prt_bytes== $past(prt_bytes1));

  assert property (state == wait_req && !prt_dv1 && prt_dv2 |=> state == serv_req2 && prt_req &&
                   prt_qos  == $past(qos2)  &&
                   prt_data == $past(prt_data2) &&
                   prt_addr == $past(prt_addr2) &&
                   prt_bytes== $past(prt_bytes2));

  // Both valid: pick higher QoS
  assert property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 > qos2) |=> state == serv_req1 && prt_req &&
                   prt_qos  == $past(qos1)  &&
                   prt_data == $past(prt_data1) &&
                   prt_addr == $past(prt_addr1) &&
                   prt_bytes== $past(prt_bytes1));

  assert property (state == wait_req && prt_dv1 && prt_dv2 && (qos2 > qos1) |=> state == serv_req2 && prt_req &&
                   prt_qos  == $past(qos2)  &&
                   prt_data == $past(prt_data2) &&
                   prt_addr == $past(prt_addr2) &&
                   prt_bytes== $past(prt_bytes2));

  // Tie QoS: alternate based on temp_state (serv_req1 -> pick 2; otherwise pick 1)
  assert property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 == qos2) && (temp_state == serv_req1) |=> state == serv_req2 && prt_req &&
                   prt_qos  == $past(qos2)  &&
                   prt_data == $past(prt_data2) &&
                   prt_addr == $past(prt_addr2) &&
                   prt_bytes== $past(prt_bytes2));

  assert property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 == qos2) && (temp_state != serv_req1) |=> state == serv_req1 && prt_req &&
                   prt_qos  == $past(qos1)  &&
                   prt_data == $past(prt_data1) &&
                   prt_addr == $past(prt_addr1) &&
                   prt_bytes== $past(prt_bytes1));

  // No request when no data valid in wait_req
  assert property (state == wait_req && !prt_dv1 && !prt_dv2 |-> !prt_req);

  // prt_req implies payload comes from one of the ports (defensive coherence)
  assert property (prt_req |-> (
                   (prt_qos==$past(qos1) && prt_data==$past(prt_data1) && prt_addr==$past(prt_addr1) && prt_bytes==$past(prt_bytes1)) ||
                   (prt_qos==$past(qos2) && prt_data==$past(prt_data2) && prt_addr==$past(prt_addr2) && prt_bytes==$past(prt_bytes2))
                 ));

  // ----------------------------------------
  // Handover on ack (service chaining)
  // ----------------------------------------
  // From serv_req1, if ack1 and dv2, immediately chain to serv_req2 with port2 payload
  assert property (state == serv_req1 && prt_ack1 && prt_dv2 |=> state == serv_req2 && prt_req &&
                   prt_qos  == $past(qos2)  &&
                   prt_data == $past(prt_data2) &&
                   prt_addr == $past(prt_addr2) &&
                   prt_bytes== $past(prt_bytes2));

  // From serv_req2, if ack2 and dv1, immediately chain to serv_req1 with port1 payload
  assert property (state == serv_req2 && prt_ack2 && prt_dv1 |=> state == serv_req1 && prt_req &&
                   prt_qos  == $past(qos1)  &&
                   prt_data == $past(prt_data1) &&
                   prt_addr == $past(prt_addr1) &&
                   prt_bytes== $past(prt_bytes1));

  // ----------------------------------------
  // Functional coverage (key intents)
  // ----------------------------------------
  cover property (state == wait_req && prt_dv1 && !prt_dv2 ##1 state == serv_req1);
  cover property (state == wait_req && !prt_dv1 && prt_dv2 ##1 state == serv_req2);
  cover property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 > qos2) ##1 state == serv_req1);
  cover property (state == wait_req && prt_dv1 && prt_dv2 && (qos2 > qos1) ##1 state == serv_req2);
  cover property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 == qos2) && temp_state == serv_req1 ##1 state == serv_req2);
  cover property (state == wait_req && prt_dv1 && prt_dv2 && (qos1 == qos2) && temp_state != serv_req1 ##1 state == serv_req1);
  cover property (state == wait_ack_low ##1 state == wait_req);
endmodule