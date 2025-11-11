// SVA monitor for Week8Lab
module Week8Lab_sva #(parameter int TERM = 216666)
(
  input logic        Clk,
  input logic        Rate,
  input logic [27:0] Count,
  input logic [1:0]  digit,
  input logic [3:0]  Anode,
  input logic [6:0]  Cathodes
);

  // Expected patterns (from DUT case statements)
  function automatic [3:0] anode_exp(input [1:0] d);
    case (d)
      2'b00: anode_exp = 4'b1110;
      2'b01: anode_exp = 4'b1101;
      2'b10: anode_exp = 4'b1011;
      default: anode_exp = 4'b0111; // 2'b11
    endcase
  endfunction

  function automatic [6:0] cath_exp(input [1:0] d);
    case (d)
      2'b00: cath_exp = 7'b0011001;
      2'b01: cath_exp = 7'b0110000;
      2'b10: cath_exp = 7'b0100100;
      default: cath_exp = 7'b1111001; // 2'b11
    endcase
  endfunction

  // Known checks
  assert property (@(posedge Clk)  !$isunknown({Count,Rate}));
  assert property (@(posedge Rate) !$isunknown({digit,Anode,Cathodes}));

  // Count range
  assert property (@(posedge Clk) Count <= TERM);

  // Count increments and Rate stable when not at terminal
  assert property (@(posedge Clk) (Count != TERM) |=> (Count == $past(Count)+1) && (Rate == $past(Rate)));

  // At terminal: Count resets and Rate toggles
  assert property (@(posedge Clk) (Count == TERM) |=> (Count == 0) && (Rate != $past(Rate)));

  // Rate edges only occur on Clk posedge
  assert property (@(posedge Rate)  $rose(Clk));
  assert property (@(negedge Rate)  $rose(Clk));

  // Exact Rate period in Clk cycles between toggles
  assert property (@(posedge Clk) $changed(Rate) |=> (! $changed(Rate))[*TERM] ##1 $changed(Rate));

  // No updates to digit/Anode/Cathodes except on Rate posedge
  assert property (@(posedge Clk) !$rose(Rate) |-> $stable({digit,Anode,Cathodes}));

  // On Rate posedge: digit increments (mod-4) and outputs match mapping for pre-increment digit
  assert property (@(posedge Rate) 1'b1 |-> ##0 (digit == $sampled(digit)+2'b01));
  assert property (@(posedge Rate) 1'b1 |-> ##0 (Anode == anode_exp($sampled(digit)) && Cathodes == cath_exp($sampled(digit))));
  // One active-low anode at a time
  assert property (@(posedge Rate) ##0 $onehot(~Anode));

  // Coverage
  cover property (@(posedge Clk)  Count == TERM);
  cover property (@(posedge Clk)  $changed(Rate));
  cover property (@(posedge Rate) $sampled(digit)==2'b00 ##1 $sampled(digit)==2'b01 ##1 $sampled(digit)==2'b10 ##1 $sampled(digit)==2'b11);

  cover property (@(posedge Rate) 1'b1 |-> ##0 (Anode==4'b1110 && Cathodes==7'b0011001)); // d=00
  cover property (@(posedge Rate) 1'b1 |-> ##0 (Anode==4'b1101 && Cathodes==7'b0110000)); // d=01
  cover property (@(posedge Rate) 1'b1 |-> ##0 (Anode==4'b1011 && Cathodes==7'b0100100)); // d=10
  cover property (@(posedge Rate) 1'b1 |-> ##0 (Anode==4'b0111 && Cathodes==7'b1111001)); // d=11

endmodule

// Bind into DUT (instantiate once per Week8Lab instance)
bind Week8Lab Week8Lab_sva #(.TERM(216666)) u_week8_sva (
  .Clk(Clk),
  .Rate(Rate),
  .Count(Count),
  .digit(digit),
  .Anode(Anode),
  .Cathodes(Cathodes)
);