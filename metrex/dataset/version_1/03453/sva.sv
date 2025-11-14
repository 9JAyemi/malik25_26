// SVA for PmodDA4_Control
// Bindable checker with concise, high-quality assertions and coverage.

module PmodDA4_Control_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [11:0] value,
  input  logic        SYNC,
  input  logic        DATA,
  input  logic        SCLK,
  input  logic [2:0]  state,
  input  logic [4:0]  index
);

  // Mirror DUT state encodings
  localparam stIDLE     = 3'd0;
  localparam stINIT_irv = 3'd1;
  localparam stTRAN_irv = 3'd2;
  localparam stINIT     = 3'd3;
  localparam stTRAN     = 3'd4;

  default clocking cb @(negedge clk); endclocking

  // Expected 32-bit shift word for current state
  function automatic logic [31:0] exp_temp (input logic [2:0] s, input logic [11:0] v);
    exp_temp = ((s == stINIT_irv) || (s == stTRAN_irv)) ? {8'h08, 24'h000001} : {12'h03F, v, 8'h00};
  endfunction

  // Basic sanity: no X/Z on key signals
  assert property ( !$isunknown({state, index, SYNC, DATA, SCLK}) );

  // SCLK is direct pass-through of clk
  assert property (@(posedge clk)  SCLK);
  assert property (@(negedge clk) !SCLK);

  // Reset behavior (synchronous to negedge)
  assert property ( rst |-> (state == stIDLE && index == 5'd31 && SYNC == 1'b0) );

  // State must stay within legal encodings
  assert property ( disable iff (rst) (state inside {stIDLE, stINIT_irv, stTRAN_irv, stINIT, stTRAN}) );

  // DATA bit must match current expected temp bit at index
  assert property ( disable iff (rst) (DATA == exp_temp(state, value)[index]) );

  // FSM transitions and outputs (use $past; protect around reset)
  // IDLE -> INIT_irv
  assert property ( disable iff (rst || $past(rst))
                    (state == stIDLE) |=> (state == stINIT_irv && index == 5'd31 && SYNC == 1'b1) );

  // INIT_irv -> TRAN_irv
  assert property ( disable iff (rst || $past(rst))
                    (state == stINIT_irv) |=> (state == stTRAN_irv && index == 5'd31 && SYNC == 1'b0) );

  // TRAN_irv counting
  assert property ( disable iff (rst || $past(rst))
                    (state == stTRAN_irv && index != 5'd0)
                    |=> (state == stTRAN_irv && index == ($past(index)-1) && SYNC == 1'b0) );

  // TRAN_irv wrap
  assert property ( disable iff (rst || $past(rst))
                    (state == stTRAN_irv && index == 5'd0)
                    |=> (state == stINIT && index == 5'd31 && SYNC == 1'b1) );

  // INIT -> TRAN
  assert property ( disable iff (rst || $past(rst))
                    (state == stINIT) |=> (state == stTRAN && index == 5'd31 && SYNC == 1'b0) );

  // TRAN counting
  assert property ( disable iff (rst || $past(rst))
                    (state == stTRAN && index != 5'd0)
                    |=> (state == stTRAN && index == ($past(index)-1) && SYNC == 1'b0) );

  // TRAN wrap
  assert property ( disable iff (rst || $past(rst))
                    (state == stTRAN && index == 5'd0)
                    |=> (state == stINIT && index == 5'd31 && SYNC == 1'b1) );

  // Minimal but meaningful coverage

  // Observe at least one IRV frame (INIT_irv -> TRAN_irv .. -> INIT)
  cover property ( disable iff (rst)
                   (state == stINIT_irv)
                   ##1 (state == stTRAN_irv)
                   ##1 (state == stTRAN_irv && index == 5'd0)
                   ##1 (state == stINIT) );

  // Observe at least one normal frame (INIT -> TRAN .. -> INIT)
  cover property ( disable iff (rst)
                   (state == stINIT)
                   ##1 (state == stTRAN)
                   ##1 (state == stTRAN && index == 5'd0)
                   ##1 (state == stINIT) );

  // See DATA toggle within a TRAN frame (exercise both 0/1 data while shifting)
  cover property ( disable iff (rst)
                   (state == stTRAN && DATA == 1'b0) ##[1:$] (state == stTRAN && DATA == 1'b1) );

endmodule

// Bind into DUT (connect to internal state/index)
bind PmodDA4_Control PmodDA4_Control_sva sva (
  .clk   (clk),
  .rst   (rst),
  .value (value),
  .SYNC  (SYNC),
  .DATA  (DATA),
  .SCLK  (SCLK),
  .state (state),
  .index (index)
);