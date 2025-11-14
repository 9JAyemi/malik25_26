// SVA for vfabric_down_converter
// Bind into DUT to observe internals (present_state, data_to_send, latch_new_data)

module vfabric_down_converter_sva #(
  parameter DATAIN_WIDTH  = 32,
  parameter DATAOUT_WIDTH = 8
)(
  input  logic                      clock,
  input  logic                      resetn,
  input  logic                      i_start,
  input  logic                      i_datain_valid,
  input  logic                      i_dataout_stall,
  input  logic [DATAIN_WIDTH-1:0]   i_datain,

  // DUT internals/outputs (connected via bind)
  input  logic [2:0]                present_state,
  input  logic [DATAIN_WIDTH-1:0]   data_to_send,
  input  logic                      latch_new_data,
  input  logic [DATAOUT_WIDTH-1:0]  o_dataout,
  input  logic                      o_dataout_valid,
  input  logic                      o_datain_stall
);

  // State encodings (match DUT)
  localparam [2:0] S_IDLE   = 3'b100;
  localparam [2:0] S_B1     = 3'b000;
  localparam [2:0] S_B2     = 3'b001;
  localparam [2:0] S_B3     = 3'b010;
  localparam [2:0] S_B4     = 3'b011;

  // Basic reset behavior
  assert property (@(posedge clock) !resetn |-> (present_state==S_IDLE && data_to_send=={DATAIN_WIDTH{1'b0}}));

  // State legality and coding sanity
  assert property (@(posedge clock) disable iff(!resetn)
                   present_state inside {S_IDLE,S_B1,S_B2,S_B3,S_B4});
  assert property (@(posedge clock) disable iff(!resetn)
                   present_state[2] |-> present_state==S_IDLE);

  // i_start gating
  assert property (@(posedge clock) disable iff(!resetn)
                   !i_start |-> (present_state==S_IDLE && o_dataout_valid==1'b0 && o_datain_stall==1'b0));

  // Latch-new-data definition and upstream stall
  assert property (@(posedge clock) disable iff(!resetn)
                   latch_new_data == ((present_state==S_IDLE) || ((present_state==S_B4) && !i_dataout_stall)));
  assert property (@(posedge clock) disable iff(!resetn)
                   o_datain_stall == (i_start ? ~latch_new_data : 1'b0));

  // data_to_send update/hold
  assert property (@(posedge clock) disable iff(!resetn)
                   (latch_new_data && i_datain_valid) |=> data_to_send == $past(i_datain));
  assert property (@(posedge clock) disable iff(!resetn)
                   !(latch_new_data && i_datain_valid) |=> data_to_send == $past(data_to_send));

  // FSM transitions (when i_start is asserted)
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_IDLE &&  i_datain_valid |=> present_state==S_B1);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_IDLE && !i_datain_valid |=> present_state==S_IDLE);

  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B1 && !i_dataout_stall |=> present_state==S_B2);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B1 &&  i_dataout_stall |=> present_state==S_B1);

  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B2 && !i_dataout_stall |=> present_state==S_B3);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B2 &&  i_dataout_stall |=> present_state==S_B2);

  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B3 && !i_dataout_stall |=> present_state==S_B4);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B3 &&  i_dataout_stall |=> present_state==S_B3);

  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B4 &&  i_dataout_stall |=> present_state==S_B4);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B4 && !i_dataout_stall &&  i_datain_valid |=> present_state==S_B1);
  assert property (@(posedge clock) disable iff(!resetn)
                   i_start && present_state==S_B4 && !i_dataout_stall && !i_datain_valid |=> present_state==S_IDLE);

  // Output valid definition
  assert property (@(posedge clock) disable iff(!resetn)
                   o_dataout_valid == (~present_state[2] & i_start));

  // Output/data stability under downstream stall
  assert property (@(posedge clock) disable iff(!resetn)
                   (~present_state[2] && i_start && i_dataout_stall)
                   |=> (present_state==$past(present_state) && o_dataout_valid && $stable(o_dataout)));

  // Byte sequencing functional check (no-stall path)
  // Verify emitted bytes match captured word in order when downstream is ready
  if (DATAIN_WIDTH==32 && DATAOUT_WIDTH==8) begin
    property p_byte_sequence_no_stall;
      logic [31:0] W;
      @(posedge clock) disable iff(!resetn)
      i_start && present_state==S_IDLE && i_datain_valid ##1
      (W = $past(i_datain), present_state==S_B1 && !i_dataout_stall && o_dataout==W[7:0]) ##1
      (present_state==S_B2 && !i_dataout_stall && o_dataout==W[15:8]) ##1
      (present_state==S_B3 && !i_dataout_stall && o_dataout==W[23:16]) ##1
      (present_state==S_B4 && !i_dataout_stall && o_dataout==W[31:24]);
    endproperty
    assert property (p_byte_sequence_no_stall);
  end

  // Coverage: basic transfer, stall mid-stream, back-to-back at B4
  cover property (@(posedge clock) disable iff(!resetn)
                  i_start && present_state==S_IDLE && i_datain_valid ##1
                  present_state==S_B1 && !i_dataout_stall ##1
                  present_state==S_B2 && !i_dataout_stall ##1
                  present_state==S_B3 && !i_dataout_stall ##1
                  present_state==S_B4 && !i_dataout_stall ##1
                  (present_state inside {S_IDLE,S_B1}));

  cover property (@(posedge clock) disable iff(!resetn)
                  i_start && present_state==S_B2 && i_dataout_stall ##1
                  i_start && present_state==S_B2 && i_dataout_stall ##1
                  i_start && present_state==S_B2 && !i_dataout_stall);

  cover property (@(posedge clock) disable iff(!resetn)
                  i_start && present_state==S_B4 && !i_dataout_stall && i_datain_valid ##1
                  present_state==S_B1);

  cover property (@(posedge clock) disable iff(!resetn)
                  i_start && present_state==S_B3 ##1 !i_start && present_state==S_IDLE);

endmodule

// Bind into the DUT (connects to internals by name)
bind vfabric_down_converter
  vfabric_down_converter_sva #(.DATAIN_WIDTH(DATAIN_WIDTH), .DATAOUT_WIDTH(DATAOUT_WIDTH))
    u_vfabric_down_converter_sva (.*);