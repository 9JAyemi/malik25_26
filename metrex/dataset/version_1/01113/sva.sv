// SVA for ps2_mouse_datain
// Bind this module to the DUT:
// bind ps2_mouse_datain ps2_mouse_datain_sva sva_inst (.*);

module ps2_mouse_datain_sva (
  input              clk,
  input              reset,
  input              wait_for_incoming_data,
  input              start_receiving_data,
  input              ps2_clk_posedge,
  input              ps2_clk_negedge, // unused by DUT but kept for bind completeness
  input              ps2_data,
  input       [7:0]  received_data,
  input              received_data_en,
  input       [2:0]  s_ps2_receiver,
  input       [3:0]  data_count,
  input       [7:0]  data_shift_reg
);

  // Mirror DUT state encodings
  localparam PS2_STATE_0_IDLE          = 3'h0;
  localparam PS2_STATE_1_WAIT_FOR_DATA = 3'h1;
  localparam PS2_STATE_2_DATA_IN       = 3'h2;
  localparam PS2_STATE_3_PARITY_IN     = 3'h3;
  localparam PS2_STATE_4_STOP_IN       = 3'h4;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity and reset
  assert property (reset |-> (s_ps2_receiver==PS2_STATE_0_IDLE && data_count==0 && data_shift_reg==0 && received_data==0 && received_data_en==0));
  assert property (!$isunknown({s_ps2_receiver, data_count, data_shift_reg, received_data, received_data_en}));
  assert property (s_ps2_receiver inside {PS2_STATE_0_IDLE,PS2_STATE_1_WAIT_FOR_DATA,PS2_STATE_2_DATA_IN,PS2_STATE_3_PARITY_IN,PS2_STATE_4_STOP_IN});

  // State transition correctness
  // IDLE transitions (precedence: wait_for_incoming_data over start_receiving_data)
  assert property ((s_ps2_receiver==PS2_STATE_0_IDLE && wait_for_incoming_data && !received_data_en) |=> s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA);
  assert property ((s_ps2_receiver==PS2_STATE_0_IDLE && !wait_for_incoming_data && start_receiving_data && !received_data_en) |=> s_ps2_receiver==PS2_STATE_2_DATA_IN);
  assert property ((s_ps2_receiver==PS2_STATE_0_IDLE && (!wait_for_incoming_data && (!start_receiving_data || received_data_en))) |=> s_ps2_receiver==PS2_STATE_0_IDLE);

  // WAIT_FOR_DATA transitions
  assert property ((s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA && (ps2_data==1'b0) && ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_2_DATA_IN);
  assert property ((s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA && !wait_for_incoming_data) |=> s_ps2_receiver==PS2_STATE_0_IDLE);
  assert property ((s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA && !(ps2_clk_posedge && (ps2_data==1'b0)) && wait_for_incoming_data) |=> s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA);

  // DATA_IN transitions
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && (data_count==3'h7) && ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_3_PARITY_IN);
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && !((data_count==3'h7) && ps2_clk_posedge)) |=> s_ps2_receiver==PS2_STATE_2_DATA_IN);

  // PARITY_IN transitions
  assert property ((s_ps2_receiver==PS2_STATE_3_PARITY_IN && ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_4_STOP_IN);
  assert property ((s_ps2_receiver==PS2_STATE_3_PARITY_IN && !ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_3_PARITY_IN);

  // STOP_IN transitions
  assert property ((s_ps2_receiver==PS2_STATE_4_STOP_IN && ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_0_IDLE);
  assert property ((s_ps2_receiver==PS2_STATE_4_STOP_IN && !ps2_clk_posedge) |=> s_ps2_receiver==PS2_STATE_4_STOP_IN);

  // data_count behavior
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && ps2_clk_posedge) |=> data_count == $past(data_count)+1);
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && !ps2_clk_posedge) |=> data_count == $past(data_count));
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN) |-> (data_count inside {[0:7]}));
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && $past(s_ps2_receiver)==PS2_STATE_2_DATA_IN && !(data_count==3'h7 && ps2_clk_posedge)) |-> data_count != 0); // no premature reset while staying in DATA_IN
  assert property (($past(s_ps2_receiver)==PS2_STATE_2_DATA_IN && s_ps2_receiver!=PS2_STATE_2_DATA_IN) |-> data_count==0); // reset on exit

  // Shift register behavior
  assert property ((s_ps2_receiver==PS2_STATE_2_DATA_IN && ps2_clk_posedge) |=> data_shift_reg == { $past(ps2_data), $past(data_shift_reg[7:1]) });
  assert property (!((s_ps2_receiver==PS2_STATE_2_DATA_IN) && ps2_clk_posedge) |=> data_shift_reg == $past(data_shift_reg)); // only updates on DATA_IN+posedge

  // received_data behavior
  assert property ((s_ps2_receiver==PS2_STATE_4_STOP_IN) |-> received_data == data_shift_reg);
  assert property ((s_ps2_receiver!=PS2_STATE_4_STOP_IN) |=> received_data == $past(received_data)); // only changes in STOP_IN

  // received_data_en exact behavior and pulse
  assert property (received_data_en == ((s_ps2_receiver==PS2_STATE_4_STOP_IN) && ps2_clk_posedge));
  assert property (received_data_en |=> !received_data_en);
  assert property (received_data_en |=> s_ps2_receiver==PS2_STATE_0_IDLE);

  // Progress: full frame generates enable pulse
  sequence eight_data_edges;
    (s_ps2_receiver==PS2_STATE_2_DATA_IN && ps2_clk_posedge)[*8];
  endsequence
  assert property ( (s_ps2_receiver==PS2_STATE_2_DATA_IN) ##0 eight_data_edges ##1 (s_ps2_receiver==PS2_STATE_3_PARITY_IN)
                    ##[1:$] (ps2_clk_posedge && s_ps2_receiver==PS2_STATE_3_PARITY_IN)
                    ##1 (s_ps2_receiver==PS2_STATE_4_STOP_IN)
                    ##[1:$] (ps2_clk_posedge && s_ps2_receiver==PS2_STATE_4_STOP_IN && received_data_en) );

  // Coverage
  cover property (s_ps2_receiver==PS2_STATE_0_IDLE ##1 s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA ##1
                  (ps2_clk_posedge && ps2_data==0 && s_ps2_receiver==PS2_STATE_1_WAIT_FOR_DATA) ##1
                  s_ps2_receiver==PS2_STATE_2_DATA_IN ##0 eight_data_edges ##1
                  (s_ps2_receiver==PS2_STATE_3_PARITY_IN && ps2_clk_posedge) ##1
                  (s_ps2_receiver==PS2_STATE_4_STOP_IN && ps2_clk_posedge && received_data_en) ##1
                  s_ps2_receiver==PS2_STATE_0_IDLE);

  cover property (s_ps2_receiver==PS2_STATE_0_IDLE ##1 (start_receiving_data && !wait_for_incoming_data) ##1
                  s_ps2_receiver==PS2_STATE_2_DATA_IN ##0 eight_data_edges ##1
                  (s_ps2_receiver==PS2_STATE_3_PARITY_IN && ps2_clk_posedge) ##1
                  (s_ps2_receiver==PS2_STATE_4_STOP_IN && ps2_clk_posedge && received_data_en));

  cover property (received_data_en && received_data==8'h00);
  cover property (received_data_en && received_data==8'hFF);
  cover property (received_data_en && received_data==8'hA5);

endmodule