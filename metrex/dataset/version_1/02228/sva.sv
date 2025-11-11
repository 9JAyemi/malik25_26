// SVA for even_parity_checker
`ifndef SYNTHESIS
module even_parity_checker_sva (
  input logic D0, D1, D2, D3, RST, ECLK, DQSW,
  input logic Q,
  input logic [3:0] data_reg
);

  default clocking cb @(posedge ECLK); endclocking

  // Reset clears state
  assert property (RST |=> (Q == 1'b0 && data_reg == 4'b0000));

  // Shift when DQSW==0
  assert property (disable iff (RST)
                   (!DQSW) |=> data_reg == { $past(data_reg)[2:0], $past(D3) });
  // Q holds on shift
  assert property (disable iff (RST)
                   (!DQSW) |=> Q == $past(Q));

  // Load on DQSW==1 and compute even parity from previous data_reg
  assert property (disable iff (RST)
                   (DQSW) |=> (data_reg == { $past(D3), $past(D2), $past(D1), $past(D0) }
                               && Q == ~^$past(data_reg)));

  // Functional coverage
  cover property (RST ##1 !RST);                       // reset pulse
  cover property (disable iff (RST) DQSW);             // load event
  cover property (disable iff (RST) !DQSW);            // shift event
  cover property (disable iff (RST) (!DQSW)[*3] ##1 DQSW); // shifts then load
  cover property (disable iff (RST) DQSW ##1 (Q == 1'b0)); // parity 0 seen
  cover property (disable iff (RST) DQSW ##1 (Q == 1'b1)); // parity 1 seen

endmodule

bind even_parity_checker even_parity_checker_sva sva_bind (.*);
`endif