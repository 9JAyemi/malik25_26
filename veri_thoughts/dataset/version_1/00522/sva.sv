// SVA for the given design. Bind to top_module.

module top_module_sva;

  default clocking cb @(posedge clk); endclocking

  // Comparator correctness and encoding
  assert property ( (A >  B) |-> comparator_output == 2'b01 );
  assert property ( (A <  B) |-> comparator_output == 2'b10 );
  assert property ( (A == B) |-> comparator_output == 2'b00 );
  assert property ( comparator_output != 2'b11 );

  // Final combinational function correctness (sampled on clk)
  assert property ( (comparator_output==2'b01)
                    |-> final_output == ({1'b0,up_down_output} + {1'b0,A}) );
  assert property ( (comparator_output==2'b10)
                    |-> final_output == ({1'b0,up_down_output} + {1'b0,B}) );
  assert property ( (comparator_output!=2'b01 && comparator_output!=2'b10)
                    |-> final_output == {2'b00,up_down_output} );

  // Up/down counter reset behavior
  assert property ( reset |-> up_down_output == 3'd0 );
  assert property ( reset && $past(reset) |-> up_down_output == 3'd0 && $stable(up_down_output) );

  // Up/down counter step (mod-8)
  assert property ( (!reset && !$past(reset) && up_down)
                    |=> up_down_output == $past(up_down_output) + 3'd1 );
  assert property ( (!reset && !$past(reset) && !up_down)
                    |=> up_down_output == $past(up_down_output) - 3'd1 );

  // Coverage
  cover property (A > B);
  cover property (A < B);
  cover property (A == B);

  cover property (comparator_output==2'b01);
  cover property (comparator_output==2'b10);
  cover property (comparator_output==2'b00);

  cover property ((!reset && !$past(reset) && $past(up_down_output)==3'd7 && up_down)
                  ##1 up_down_output==3'd0);
  cover property ((!reset && !$past(reset) && $past(up_down_output)==3'd0 && !up_down)
                  ##1 up_down_output==3'd7);

  cover property (comparator_output==2'b01 &&
                  ({1'b0,up_down_output}+{1'b0,A})[4]); // carry-out when adding A
  cover property (comparator_output==2'b10 &&
                  ({1'b0,up_down_output}+{1'b0,B})[4]); // carry-out when adding B
  cover property (comparator_output==2'b00 && final_output=={2'b00,up_down_output});

endmodule

bind top_module top_module_sva tmsva();