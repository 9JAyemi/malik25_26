//====================================================
// SVA for top_module
//====================================================
module top_module_sva;
  // Use DUT's scope via bind; no ports needed
  default clocking cb @(posedge clk); endclocking

  // Combinational mux correctness
  assert property (disable iff (reset)
    mux_output == (select ? shifted_value : d)
  );

  // Synchronous reset clears sequential state (checked next cycle)
  assert property ($past(reset) |-> (shifted_value==8'b0 &&
                                     shift_reg1_out==4'b0 &&
                                     shift_reg2_out==4'b0 &&
                                     q==4'b0));

  // shifted_value update function (use $past to avoid sampling order issues)
  assert property ((!reset && !$past(reset)) |->
    shifted_value == {2'b00, $past(d[1]), $past(d[0]), 2'b11, 2'b00}
  );

  // Shift-register capture mapping
  assert property ((!reset && !$past(reset)) |->
    shift_reg1_out == { $past(mux_output[0]),
                        $past(mux_output[1]),
                        $past(mux_output[2]),
                        $past(mux_output[3]) }
  );
  assert property ((!reset && !$past(reset)) |->
    shift_reg2_out == { $past(mux_output[4]),
                        $past(mux_output[5]),
                        $past(mux_output[6]),
                        $past(mux_output[7]) }
  );

  // XOR correctness (structural)
  assert property (disable iff (reset)
    q == (shift_reg1_out ^ shift_reg2_out)
  );

  // XOR correctness from mux source bits
  assert property ((!reset && !$past(reset)) |->
    q == { $past(mux_output[0]) ^ $past(mux_output[4]),
           $past(mux_output[1]) ^ $past(mux_output[5]),
           $past(mux_output[2]) ^ $past(mux_output[6]),
           $past(mux_output[3]) ^ $past(mux_output[7]) }
  );

  // No X/Z after reset deasserted
  assert property (disable iff (reset)
    !$isunknown({shifted_value, mux_output, shift_reg1_out, shift_reg2_out, q})
  );

  // Key coverage
  cover property ($rose(reset));
  cover property ($fell(reset));
  cover property ((!$past(reset)) && !reset && ($past(select)==1));
  cover property ((!$past(reset)) && !reset && ($past(select)==0));
  cover property (q == 4'b0000);
  cover property (q != 4'b0000);
  cover property ($rose(q[0]));
  cover property ($rose(q[1]));
  cover property ($rose(q[2]));
  cover property ($rose(q[3]));
  cover property (!reset && d[1:0]==2'b00);
  cover property (!reset && d[1:0]==2'b01);
  cover property (!reset && d[1:0]==2'b10);
  cover property (!reset && d[1:0]==2'b11);
endmodule

bind top_module top_module_sva sva_top_module_inst();

//====================================================
// SVA for my_dff (leaf checker)
//====================================================
module my_dff_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset drives q to 0 on next cycle
  assert property ($past(reset) |-> q==1'b0);

  // Capture behavior: q follows d with 1-cycle latency
  assert property ((!reset && !$past(reset)) |-> q==$past(d));

  // No X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({d,q}));

  // Simple coverage
  cover property ($rose(q));
  cover property ($fell(q));
endmodule

bind my_dff my_dff_sva sva_my_dff_inst();