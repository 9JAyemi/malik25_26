module moore_fsm_sva (
  input logic clk,
  input logic rst,
  input logic i_input,
  input logic o_output,
  input logic [2:0] o_current_state,
  input logic [2:0] o_next_state
);
  // Local copies of DUT constants for readability
  localparam logic [2:0] STATE_U = 3'b000;
  localparam logic [2:0] STATE_V = 3'b001;
  localparam logic [2:0] STATE_W = 3'b010;
  localparam logic [2:0] STATE_X = 3'b011;
  localparam logic [2:0] STATE_Y = 3'b100;
  localparam logic [2:0] STATE_Z = 3'b101;

  ///// State register behavior /////
  // On non-reset cycles (following a non-reset cycle), current_state updates from prior next_state.
  check_state_updates_from_next: assert property (
    @(posedge clk) disable iff (rst) $past(!rst) |-> (o_current_state == $past(o_next_state))
  );

  ///// Next-state combinational mapping /////
  // For STATE_U: 0->Z, 1->W.
  map_next_from_U: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_U) |-> (o_next_state == (i_input ? STATE_W : STATE_Z))
  );
  // For STATE_V: 0->Z, 1->W.
  map_next_from_V: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_V) |-> (o_next_state == (i_input ? STATE_W : STATE_Z))
  );
  // For STATE_W: 0->X, 1->U.
  map_next_from_W: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_W) |-> (o_next_state == (i_input ? STATE_U : STATE_X))
  );
  // For STATE_X: 0->Y, 1->X (self-loop on 1).
  map_next_from_X: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_X) |-> (o_next_state == (i_input ? STATE_X : STATE_Y))
  );
  // For STATE_Y: 0->V, 1->Y (self-loop on 1).
  map_next_from_Y: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_Y) |-> (o_next_state == (i_input ? STATE_Y : STATE_V))
  );
  // For STATE_Z: 0->Y, 1->X.
  map_next_from_Z: assert property (
    @(posedge clk) disable iff (rst) (o_current_state == STATE_Z) |-> (o_next_state == (i_input ? STATE_X : STATE_Y))
  );
  // For invalid states (110/111): default goes to STATE_U.
  map_next_from_invalid_to_U: assert property (
    @(posedge clk) disable iff (rst) (o_current_state inside {3'b110,3'b111}) |-> (o_next_state == STATE_U)
  );
  // next_state is always one of the defined encodings.
  check_next_state_legal: assert property (
    @(posedge clk) disable iff (rst) (o_next_state inside {STATE_U,STATE_V,STATE_W,STATE_X,STATE_Y,STATE_Z})
  );

  ///// Moore output mapping /////
  // For U/Y/Z, output must be 1.
  check_output_high_states: assert property (
    @(posedge clk) disable iff (rst) (o_current_state inside {STATE_U,STATE_Y,STATE_Z}) |-> (o_output == 1'b1)
  );
  // For V/W/X, output must be 0.
  check_output_low_states: assert property (
    @(posedge clk) disable iff (rst) (o_current_state inside {STATE_V,STATE_W,STATE_X}) |-> (o_output == 1'b0)
  );

  ///// Reset behavior /////
  // After a rising reset, current_state must be STATE_U by the next clock edge.
  reset_sets_state_U_next_cycle: assert property (
    @(posedge clk) $rose(rst) |-> ##1 (o_current_state == STATE_U)
  );

endmodule