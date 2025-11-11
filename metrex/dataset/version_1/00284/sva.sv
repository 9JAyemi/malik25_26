// Bindable SVA for mc_ctrl. Bind as shown at the bottom.
module mc_ctrl_sva #(
  parameter IDLE    = 3'd0,
  parameter TQ_LUMA = 3'd1,
  parameter MC_CB   = 3'd2,
  parameter TQ_CB   = 3'd3,
  parameter MC_CR   = 3'd4,
  parameter TQ_CR   = 3'd5,
  parameter DONE    = 3'd6
) (
  input  logic         clk,
  input  logic         rstn,
  input  logic         mc_start_i,
  input  logic         mc_done_o,
  input  logic         mvd_access_o,
  input  logic         chroma_start_o,
  input  logic         chroma_sel_o,
  input  logic         chroma_done_i,
  input  logic         tq_start_o,
  input  logic  [1:0]  tq_sel_o,
  input  logic         tq_done_i,
  input  logic  [2:0]  current_state,
  input  logic  [2:0]  next_state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rstn)

  // Reset behavior (checked even during reset)
  assert property (@(posedge clk) !rstn |-> current_state == IDLE);

  // State legality
  assert property (current_state inside {IDLE,TQ_LUMA,MC_CB,TQ_CB,MC_CR,TQ_CR,DONE});
  assert property (next_state   inside {IDLE,TQ_LUMA,MC_CB,TQ_CB,MC_CR,TQ_CR,DONE});

  // Next-state sequencing on each state
  assert property ( (current_state==IDLE     &&  mc_start_i) |=> current_state==TQ_LUMA );
  assert property ( (current_state==IDLE     && !mc_start_i) |=> current_state==IDLE    );

  assert property ( (current_state==TQ_LUMA  &&  tq_done_i ) |=> current_state==MC_CB   );
  assert property ( (current_state==TQ_LUMA  && !tq_done_i ) |=> current_state==TQ_LUMA );

  assert property ( (current_state==MC_CB    &&  chroma_done_i) |=> current_state==TQ_CB );
  assert property ( (current_state==MC_CB    && !chroma_done_i) |=> current_state==MC_CB );

  assert property ( (current_state==TQ_CB    &&  tq_done_i ) |=> current_state==MC_CR   );
  assert property ( (current_state==TQ_CB    && !tq_done_i ) |=> current_state==TQ_CB   );

  assert property ( (current_state==MC_CR    &&  chroma_done_i) |=> current_state==TQ_CR );
  assert property ( (current_state==MC_CR    && !chroma_done_i) |=> current_state==MC_CR );

  assert property ( (current_state==TQ_CR    &&  tq_done_i ) |=> current_state==DONE    );
  assert property ( (current_state==TQ_CR    && !tq_done_i ) |=> current_state==TQ_CR   );

  assert property ( (current_state==DONE) |=> current_state==IDLE );

  // Output equivalence to spec
  assert property ( mc_done_o      == (current_state==DONE) );
  assert property ( mvd_access_o   == (current_state==TQ_LUMA) );
  assert property ( chroma_sel_o   == (current_state==MC_CR) );

  assert property ( chroma_start_o == ((current_state==TQ_LUMA && tq_done_i) ||
                                       (current_state==TQ_CB   && tq_done_i)) );

  assert property ( tq_start_o     == ((current_state==IDLE   && mc_start_i)      ||
                                       (current_state==MC_CB  && chroma_done_i)   ||
                                       (current_state==MC_CR  && chroma_done_i)) );

  // tq_sel encoding and mapping
  assert property ( tq_sel_o inside {2'b00,2'b10,2'b11} );
  assert property (
      ((current_state==TQ_LUMA) && (tq_sel_o==2'b00)) ||
      ((current_state==TQ_CB  ) && (tq_sel_o==2'b10)) ||
      ((current_state==TQ_CR  ) && (tq_sel_o==2'b11)) ||
      ((current_state inside {IDLE,MC_CB,MC_CR,DONE}) && (tq_sel_o==2'b00))
  );

  // Mutually exclusive start strobes and single-cycle pulse checks
  assert property ( !(tq_start_o && chroma_start_o) );
  assert property ( tq_start_o     |=> !tq_start_o );
  assert property ( chroma_start_o |=> !chroma_start_o );
  assert property ( mc_done_o      |=> !mc_done_o );

  // Known-value check on key outputs and states
  assert property ( !$isunknown({current_state,next_state,tq_sel_o,
                                 mc_done_o,mvd_access_o,chroma_sel_o,
                                 chroma_start_o,tq_start_o}) );

  // Full operation coverage: IDLE -> ... -> DONE -> IDLE with proper handshakes
  sequence full_flow;
    (current_state==IDLE && mc_start_i)
    ##1 (current_state==TQ_LUMA)
    ##[1:$] (current_state==TQ_LUMA && tq_done_i) ##1 (current_state==MC_CB)
    ##[1:$] (current_state==MC_CB   && chroma_done_i) ##1 (current_state==TQ_CB)
    ##[1:$] (current_state==TQ_CB   && tq_done_i) ##1 (current_state==MC_CR)
    ##[1:$] (current_state==MC_CR   && chroma_done_i) ##1 (current_state==TQ_CR)
    ##[1:$] (current_state==TQ_CR   && tq_done_i) ##1 (current_state==DONE)
    ##1 (current_state==IDLE);
  endsequence
  cover property (full_flow);

  // Coverage for both chroma_start_o pulses and all tq_start_o pulses
  cover property (current_state==TQ_LUMA && tq_done_i && chroma_start_o);
  cover property (current_state==TQ_CB   && tq_done_i && chroma_start_o);
  cover property (current_state==IDLE  && mc_start_i    && tq_start_o);
  cover property (current_state==MC_CB && chroma_done_i && tq_start_o);
  cover property (current_state==MC_CR && chroma_done_i && tq_start_o);
  cover property (current_state==MC_CR && chroma_sel_o);

endmodule

// Example bind (place in a testbench or a separate bind file):
// bind mc_ctrl mc_ctrl_sva #(.IDLE(IDLE),.TQ_LUMA(TQ_LUMA),.MC_CB(MC_CB),.TQ_CB(TQ_CB),.MC_CR(MC_CR),.TQ_CR(TQ_CR),.DONE(DONE))
//   u_mc_ctrl_sva(.*,.current_state(current_state),.next_state(next_state));