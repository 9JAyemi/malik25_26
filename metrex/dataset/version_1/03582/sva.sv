// SVA for _4bit_binary_multiplier
`ifndef _4BIT_BINARY_MULTIPLIER_SVA
`define _4BIT_BINARY_MULTIPLIER_SVA

module _4bit_binary_multiplier_sva;

  // Bound into _4bit_binary_multiplier: direct access to DUT signals
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic sanity
  assert property (start |-> !$isunknown({multiplier_address, multiplicand_address}));
  assert property (p == product);

  // Start behavior: latch operands and clear state
  assert property (start |-> multiplier == multiplier_address
                            && multiplicand == multiplicand_address
                            && counter == 4'd0
                            && product == 8'h00
                            && done == 1'b0);

  // Counter must increment every cycle without start (mod-16)
  assert property (!start |-> counter == $past(counter) + 4'd1);

  // Done timing and stickiness
  assert property ($fell(start) |-> !done[*4] ##1 done);        // exactly 5 cycles after falling edge of start
  assert property ($rose(done) |-> $past(counter) == 4'd4);
  assert property (($past(counter) == 4'd4) && !start |-> done); // when pre-counter==4, done must be 1 this cycle
  assert property (done && !start |=> done);                     // stays high until next start
  assert property (start |-> !done);                             // cleared on start

  // Datapath NBA relationships
  assert property (!start |-> adder_output == $past(adder_input) + $past(shift_input));
  assert property (!start |-> shift_output == $past(shift_reg[3]));
  assert property (!start |-> shift_reg[3] == $past(shift_reg[2])
                             && shift_reg[2] == $past(shift_reg[1])
                             && shift_reg[1] == $past(shift_reg[0])
                             && shift_reg[0] == $past(adder_output[3:0]));

  // Branch behavior based on previous counter value
  assert property (!start && $past(counter)==4'd0 |-> adder_input==4'b0000
                                               &&  shift_input==$past(multiplicand));
  assert property (!start && $past(counter)!=4'd0 |-> adder_input == { $past(shift_output)[2:0],
                                                                       $past(multiplier)[$past(counter)-1] }
                                               &&  shift_input == $past(shift_reg_output));

  // Explicit checks for width/truncation effects present in DUT
  assert property (!start |-> shift_reg_output == { $past(shift_reg[1]), $past(shift_reg[0]) });
  assert property (!start |-> product == { $past(shift_reg_output)[3:0], $past(adder_output)[7:4] });

  // Functional correctness: final product
  assert property ($rose(done) |-> p == multiplier * multiplicand);

  // Coverage
  cover property ($fell(start) ##5 done);
  cover property ($fell(start) ##5 (done && p == multiplier * multiplicand));
  cover property (start && multiplier_address==4'h0 && multiplicand_address==4'h0);
  cover property (start && multiplier_address==4'hF && multiplicand_address==4'hF);
  cover property (start && multiplier_address==4'h0 && multiplicand_address==4'hF);
  cover property (start && multiplier_address==4'hF && multiplicand_address==4'h0);
  cover property (!start && $past(counter)!=4'd0); // exercises nonzero branch

endmodule

bind _4bit_binary_multiplier _4bit_binary_multiplier_sva sva();

`endif