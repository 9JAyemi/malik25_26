// SVA for verilog_module
module verilog_module_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (checked even during reset)
  assert property (@(posedge clk) disable iff (1'b0) (reset |-> icap_state==ICAP_IDLE));

  // State validity
  assert property (icap_state inside {ICAP_IDLE,ICAP_WR0,ICAP_WR1,ICAP_RD0,ICAP_RD1});

  // Next-state rules
  assert property ((icap_state==ICAP_IDLE && cyc_i && stb_i && we_i)  |=> icap_state==ICAP_WR0);
  assert property ((icap_state==ICAP_IDLE && cyc_i && stb_i && !we_i) |=> icap_state==ICAP_RD0);
  assert property ((icap_state==ICAP_IDLE && !(cyc_i && stb_i))       |=> icap_state==ICAP_IDLE);
  assert property ((icap_state==ICAP_WR0) |=> icap_state==ICAP_WR1);
  assert property ((icap_state==ICAP_WR1) |=> icap_state==ICAP_IDLE);
  assert property ((icap_state==ICAP_RD0) |=> icap_state==ICAP_RD1);
  assert property ((icap_state==ICAP_RD1) |=> icap_state==ICAP_IDLE);

  // Derived signals correctness
  assert property (ack_o == ((icap_state==ICAP_WR1)||(icap_state==ICAP_RD1)));
  assert property (CE    == ((icap_state==ICAP_WR1)||(icap_state==ICAP_RD0)));
  assert property (WRITE == ((icap_state==ICAP_WR0)||(icap_state==ICAP_WR1)));

  // Handshake latency and pulse width
  sequence s_req; (icap_state==ICAP_IDLE && cyc_i && stb_i); endsequence
  assert property (s_req |-> ##2 ack_o);
  assert property (ack_o |-> $past(s_req,2));
  assert property (ack_o |=> !ack_o);
  assert property (ack_o |-> !$past(ack_o));

  // Datapath mapping
  assert property ((!CE)            |-> (dat_o === dat_i));
  assert property ((CE && !WRITE)   |-> (dat_o === 32'h0000_0000));
  assert property ((CE &&  WRITE)   |-> (dat_o === 32'h0000_0001));

  // X-checks on controls
  assert property (!$isunknown({icap_state,CE,WRITE,ack_o}));

  // Coverage
  cover property ((icap_state==ICAP_IDLE && cyc_i && stb_i && we_i)
                  ##1 (icap_state==ICAP_WR0)
                  ##1 (icap_state==ICAP_WR1 && ack_o)
                  ##1 (icap_state==ICAP_IDLE));
  cover property ((icap_state==ICAP_IDLE && cyc_i && stb_i && !we_i)
                  ##1 (icap_state==ICAP_RD0)
                  ##1 (icap_state==ICAP_RD1 && ack_o)
                  ##1 (icap_state==ICAP_IDLE));
  cover property (CE && !WRITE && dat_o==32'h0);
  cover property (CE &&  WRITE && dat_o==32'h1);
  cover property (!CE && (dat_o===dat_i));
endmodule

bind verilog_module verilog_module_sva sva_i();