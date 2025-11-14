// SVA for Stack: concise, high-value checks and coverage.
// Bind this to the DUT to access internal state, including the data array.

`ifndef STACK_SVA_SV
`define STACK_SVA_SV

module Stack_sva #(parameter DEPTH=8)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [1:0]        stackCntrl,
  input  logic [11:0]       pushValue,
  input  logic [2:0]        stackPntr,
  input  logic [11:0]       popValue,
  input  logic [11:0]       data [0:DEPTH-1]
);
  localparam PUSH = 2'b01;
  localparam POP  = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Synchronous check of reset effect (override default disable)
  assert property (@(posedge clk) disable iff (1'b0)
                   rst |-> (stackPntr==3'd0 && (foreach (data[i]) data[i]==12'd0)));

  // Pointer range (safety)
  assert property (stackPntr < 3'd8);

  // Push: pointer increments and writeback is pushValue+1 at prior pointer
  assert property ( (stackCntrl==PUSH && stackPntr<3'd7) |=> stackPntr == $past(stackPntr)+1 );
  assert property ( (stackCntrl==PUSH && stackPntr<3'd7) |=> data[$past(stackPntr)] == $past(pushValue)+12'd1 );
  // popValue must not change on push
  assert property ( (stackCntrl==PUSH) |=> $stable(popValue) );

  // Pop: pointer decrements and popValue returns top element (LIFO)
  assert property ( (stackCntrl==POP && stackPntr>3'd0) |=> stackPntr == $past(stackPntr)-1 );
  assert property ( (stackCntrl==POP && stackPntr>3'd0) |=> popValue == $past(data[$past(stackPntr)-1]) );

  // No memory writes on POP
  genvar i;
  generate
    for (i=0;i<DEPTH;i++) begin : g_mem_stable_on_pop
      assert property ( (stackCntrl==POP) |=> $stable(data[i]) );
    end
  endgenerate

  // No-ops (00/11): all state stable
  assert property ( (stackCntrl inside {2'b00,2'b11}) |=> $stable(stackPntr) && $stable(popValue) );
  generate
    for (i=0;i<DEPTH;i++) begin : g_mem_stable_on_noop
      assert property ( (stackCntrl inside {2'b00,2'b11}) |=> $stable(data[i]) );
    end
  endgenerate

  // Overflow attempt (full push): no state change
  assert property ( (stackCntrl==PUSH && stackPntr==3'd7) |=> stackPntr==3'd7 && $stable(popValue) );
  generate
    for (i=0;i<DEPTH;i++) begin : g_mem_stable_on_full_push
      assert property ( (stackCntrl==PUSH && stackPntr==3'd7) |=> $stable(data[i]) );
    end
  endgenerate

  // Underflow attempt (empty pop): no state change
  assert property ( (stackCntrl==POP && stackPntr==3'd0) |=> stackPntr==3'd0 && $stable(popValue) );
  generate
    for (i=0;i<DEPTH;i++) begin : g_mem_stable_on_empty_pop
      assert property ( (stackCntrl==POP && stackPntr==3'd0) |=> $stable(data[i]) );
    end
  endgenerate

  // Coverage: reach full
  cover property ( (stackCntrl==PUSH && stackPntr==3'd6) ##1 (stackPntr==3'd7) );
  // Coverage: reach empty from 1
  cover property ( (stackCntrl==POP  && stackPntr==3'd1) ##1 (stackPntr==3'd0) );
  // Coverage: overflow and underflow attempts
  cover property ( (stackCntrl==PUSH && stackPntr==3'd7) );
  cover property ( (stackCntrl==POP  && stackPntr==3'd0) );
  // Coverage: immediate push then pop returns the pushed value (+1)
  cover property ( (stackCntrl==PUSH && stackPntr<3'd7) ##1
                   (stackCntrl==POP  && $past(stackPntr)>3'd0) ##1
                   (popValue == $past(pushValue)+12'd1) );

endmodule

// Bind into the DUT (accesses internal array "data")
bind Stack Stack_sva #(.DEPTH(8)) u_stack_sva (
  .clk(clk),
  .rst(rst),
  .stackCntrl(stackCntrl),
  .pushValue(pushValue),
  .stackPntr(stackPntr),
  .popValue(popValue),
  .data(data)
);

`endif