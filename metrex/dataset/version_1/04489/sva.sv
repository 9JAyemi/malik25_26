// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic [7:0]  d,
  input logic [7:0]  q,
  input logic [2:0]  counter,
  input logic [7:0]  dff_data
);

  default clocking cb @(negedge clk); endclocking

  // q mirrors dff_data (combinational assign)
  assert property (q == dff_data)
    else $error("q must mirror dff_data");

  // State updates only on negedge
  assert property (@(posedge clk) $stable(counter) && $stable(dff_data) && $stable(q))
    else $error("State changed outside negedge");

  // Counter next-state: +1 mod 8
  assert property ( !$isunknown($past(counter))
                    |-> counter == (($past(counter)==3'b111) ? 3'b000 : $past(counter)+3'b001) )
    else $error("Counter next-state incorrect");

  // Wrap behavior (7 -> 0) clears dff_data
  assert property ( !$isunknown($past(counter)) && $past(counter)==3'b111
                    |-> (counter==3'b000 && dff_data==8'h00) )
    else $error("Wrap/clear behavior incorrect");

  // Shift/insert when not wrapping
  assert property ( !$isunknown($past(counter)) && $past(counter)!=3'b111 &&
                    !$isunknown($past(dff_data)) && !$isunknown($past(d))
                    |-> (dff_data == { $past(dff_data[6:0]), $past(d[7]) }) )
    else $error("Shift/insert behavior incorrect");

  // Coverage: see wrap with clear
  cover property ( !$isunknown($past(counter)) && $past(counter)==3'b111
                   ##0 (counter==3'b000 && dff_data==8'h00) );

  // Coverage: see both inserted 0 and 1 into LSB on shift
  cover property ( !$isunknown($past(counter)) && $past(counter)!=3'b111 &&
                   !$isunknown($past(d)) && $past(d[7])==1'b0 && dff_data[0]==1'b0 );
  cover property ( !$isunknown($past(counter)) && $past(counter)!=3'b111 &&
                   !$isunknown($past(d)) && $past(d[7])==1'b1 && dff_data[0]==1'b1 );

  // Coverage: observe a full counter cycle 0..7->0
  cover property ( counter==3'b000 ##1 counter==3'b001 ##1 counter==3'b010 ##1 counter==3'b011 ##1
                   counter==3'b100 ##1 counter==3'b101 ##1 counter==3'b110 ##1 counter==3'b111 ##1 counter==3'b000 );

endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .d(d),
  .q(q),
  .counter(counter),
  .dff_data(dff_data)
);