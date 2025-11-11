// SVA for EHR_8
module EHR_8_sva #(
  parameter DATA_SZ   = 1,
  parameter RESET_VAL = 0
)(
  input logic                 CLK,
  input logic                 RST_N,
  input logic [DATA_SZ-1:0]   read_0, read_1, read_2, read_3, read_4, read_5, read_6, read_7,
  input logic [DATA_SZ-1:0]   write_0, write_1, write_2, write_3, write_4, write_5, write_6, write_7,
  input logic                 EN_write_0, EN_write_1, EN_write_2, EN_write_3,
                              EN_write_4, EN_write_5, EN_write_6, EN_write_7,
  input logic [DATA_SZ-1:0]   r
);
  default clocking cb @(posedge CLK); endclocking

  // Combinational read-chain correctness
  a_read0: assert property (read_0 == r);
  a_chain0: assert property (read_1 == (EN_write_0 ? write_0 : read_0));
  a_chain1: assert property (read_2 == (EN_write_1 ? write_1 : read_1));
  a_chain2: assert property (read_3 == (EN_write_2 ? write_2 : read_2));
  a_chain3: assert property (read_4 == (EN_write_3 ? write_3 : read_3));
  a_chain4: assert property (read_5 == (EN_write_4 ? write_4 : read_4));
  a_chain5: assert property (read_6 == (EN_write_5 ? write_5 : read_5));
  a_chain6: assert property (read_7 == (EN_write_6 ? write_6 : read_6));

  // Next-state register behavior
  a_reset_next: assert property (!RST_N |=> r == RESET_VAL);
  a_next_from_chain: assert property (RST_N |=> r == $past(EN_write_7 ? write_7 : read_7));
  a_no_write_hold: assert property (RST_N && !(EN_write_0|EN_write_1|EN_write_2|EN_write_3|
                                               EN_write_4|EN_write_5|EN_write_6|EN_write_7)
                                    |=> r == $past(r));

  // Basic X-checks on controls when out of reset
  a_ctrl_known: assert property (RST_N |-> !$isunknown({EN_write_0,EN_write_1,EN_write_2,EN_write_3,
                                                        EN_write_4,EN_write_5,EN_write_6,EN_write_7})));

  // Coverage: each priority level wins, no-write hold, and multi-write priority
  c_no_write_hold: cover property (RST_N && !(EN_write_0|EN_write_1|EN_write_2|EN_write_3|
                                              EN_write_4|EN_write_5|EN_write_6|EN_write_7)
                                   ##1 r == $past(r));
  c_w7: cover property (RST_N && EN_write_7 ##1 r == $past(write_7));
  c_w6: cover property (RST_N && EN_write_6 && !EN_write_7 ##1 r == $past(write_6));
  c_w5: cover property (RST_N && EN_write_5 && !(EN_write_6|EN_write_7) ##1 r == $past(write_5));
  c_w4: cover property (RST_N && EN_write_4 && !(EN_write_5|EN_write_6|EN_write_7) ##1 r == $past(write_4));
  c_w3: cover property (RST_N && EN_write_3 && !(EN_write_4|EN_write_5|EN_write_6|EN_write_7) ##1 r == $past(write_3));
  c_w2: cover property (RST_N && EN_write_2 && !(EN_write_3|EN_write_4|EN_write_5|EN_write_6|EN_write_7) ##1 r == $past(write_2));
  c_w1: cover property (RST_N && EN_write_1 && !(EN_write_2|EN_write_3|EN_write_4|EN_write_5|EN_write_6|EN_write_7) ##1 r == $past(write_1));
  c_w0: cover property (RST_N && EN_write_0 && !(EN_write_1|EN_write_2|EN_write_3|EN_write_4|EN_write_5|EN_write_6|EN_write_7) ##1 r == $past(write_0));
  c_all_multi_priority: cover property (RST_N && (EN_write_0&EN_write_1&EN_write_2&EN_write_3&
                                                  EN_write_4&EN_write_5&EN_write_6&EN_write_7)
                                       ##1 r == $past(write_7));
endmodule

bind EHR_8 EHR_8_sva #(.DATA_SZ(DATA_SZ), .RESET_VAL(RESET_VAL)) u_ehr_8_sva (.*);