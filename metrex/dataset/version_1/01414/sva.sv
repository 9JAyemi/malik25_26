// SVA for UpDownCtr
module UpDownCtr_sva (
  input        clock,
  input        reset,
  input  [9:0] io_strideInc,
  input  [9:0] io_strideDec,
  input        io_inc,
  input        io_dec,
  input  [9:0] io_out,
  input  [9:0] io_nextInc,
  input  [9:0] io_nextDec
);

  default clocking cb @(posedge clock); endclocking

  // Combinational outputs check
  assert property (io_out == io_out); // placeholder for clocking; always true
  assert property (io_nextInc == (io_out + io_strideInc));
  assert property (io_nextDec == (io_out - io_strideDec));

  // Synchronous reset behavior
  assert property (reset |=> (io_out == 10'h000));
  assert property ((reset && $past(reset)) |-> (io_out == 10'h000));

  // Next-state functional update (covers all inc/dec combinations)
  assert property ((!reset && !$past(reset))
                   |-> io_out
                       == $past(io_out)
                          + ($past(io_inc) ? $past(io_strideInc) : 10'd0)
                          - ($past(io_dec) ? $past(io_strideDec) : 10'd0));

  // Optional specialized holds (concise sanity)
  assert property ((!reset && !$past(reset) && !$past(io_inc) && !$past(io_dec))
                   |-> (io_out == $past(io_out)));

  // Coverage: reset seen
  cover property ($rose(reset));
  cover property ($fell(reset));

  // Coverage: operation modes
  cover property (disable iff (reset) ($past(!reset) && $past(!io_inc && !io_dec)));
  cover property (disable iff (reset) ($past(!reset) && $past( io_inc && !io_dec)));
  cover property (disable iff (reset) ($past(!reset) && $past(!io_inc &&  io_dec)));
  cover property (disable iff (reset) ($past(!reset) && $past( io_inc &&  io_dec)));

  // Coverage: wrap-around scenarios
  localparam [9:0] MAX = 10'h3FF;
  cover property (disable iff (reset)
                  ($past(!reset) && $past(io_inc && !io_dec)
                   && ($past(io_out) > (MAX - $past(io_strideInc)))));
  cover property (disable iff (reset)
                  ($past(!reset) && $past(io_dec && !io_inc)
                   && ($past(io_out) < $past(io_strideDec))));

endmodule

bind UpDownCtr UpDownCtr_sva sva (
  .clock      (clock),
  .reset      (reset),
  .io_strideInc(io_strideInc),
  .io_strideDec(io_strideDec),
  .io_inc     (io_inc),
  .io_dec     (io_dec),
  .io_out     (io_out),
  .io_nextInc (io_nextInc),
  .io_nextDec (io_nextDec)
);