// SystemVerilog Assertions for the provided design
// Focused, high-quality checks and concise functional coverage

// ------------------------
// parallel_load_shift SVA
// ------------------------
module parallel_load_shift_chk (
  input clk,
  input reset,
  input [7:0] data_in,
  input [2:0] shift_amount,
  input [7:0] shift_out
);
  // Known/valid inputs on clock
  assert property (@(posedge clk) !$isunknown({reset, shift_amount, data_in}));

  // Reset behavior
  assert property (@(posedge clk) reset |-> shift_out == 8'h00);
  assert property (@(posedge clk) $rose(reset) |=> shift_out == 8'h00);

  // Next-state functional check (matches the RTL assignment semantics with truncation to 8 LSBs)
  let exp_concat = { $past(shift_out)[7-$past(shift_amount):0], $past(data_in) };
  assert property (@(posedge clk) disable iff (reset)
                   $past(!reset) |-> shift_out == exp_concat[7:0]);

  // Lightweight coverage
  // - Exercise all shift_amount values
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : cov_amt
      cover property (@(posedge clk) disable iff (reset) shift_amount == i[2:0]);
    end
  endgenerate
  // - Observe output activity
  cover property (@(posedge clk) disable iff (reset) $changed(shift_out));
endmodule

bind parallel_load_shift parallel_load_shift_chk
  (.clk(clk), .reset(reset), .data_in(data_in), .shift_amount(shift_amount), .shift_out(shift_out));


// ------------------------
// top-level SVA
// ------------------------
module top_module_chk (
  input clk,
  input reset,
  input [49:0] in,
  input select,
  input [7:0] shift_out,
  input out_nand,
  input out_nor,
  input out_xnor,
  input [49:0] final_output,
  input [49:0] in_wire,
  input [7:0]  shift_out_wire
);
  // Basic X checks on key signals at sample time
  assert property (@(posedge clk) !$isunknown({reset, in, select, shift_out}));

  // Internal mux correctness
  assert property (@(posedge clk) in_wire == (select ? 50'b0 : in));

  // Connectivity: shift_out mirrors internal wire
  assert property (@(posedge clk) shift_out == shift_out_wire);

  // Combinational block correctness (sampled on clk)
  assert property (@(posedge clk) out_nand == ~(&in));
  assert property (@(posedge clk) out_nor  == ~(|in));
  assert property (@(posedge clk) out_xnor == ~(^in));

  // Functional module correctness and width semantics
  let zext_shift_out = {42'b0, shift_out};
  assert property (@(posedge clk) final_output == (zext_shift_out & in_wire));
  assert property (@(posedge clk) final_output[49:8] == '0);

  // Coverage: select both ways and transitions
  cover property (@(posedge clk) select == 1);
  cover property (@(posedge clk) select == 0);
  cover property (@(posedge clk) $rose(select));
  cover property (@(posedge clk) $fell(select));

  // Coverage: combinational outputs hit both 0 and 1
  cover property (@(posedge clk) out_nand == 0);
  cover property (@(posedge clk) out_nand == 1);
  cover property (@(posedge clk) out_nor  == 0);
  cover property (@(posedge clk) out_nor  == 1);
  cover property (@(posedge clk) out_xnor == 0);
  cover property (@(posedge clk) out_xnor == 1);

  // Coverage: final_output drives zero and non-zero
  cover property (@(posedge clk) final_output == '0);
  cover property (@(posedge clk) final_output != '0);
endmodule

bind top_module top_module_chk
  (.clk(clk),
   .reset(reset),
   .in(in),
   .select(select),
   .shift_out(shift_out),
   .out_nand(out_nand),
   .out_nor(out_nor),
   .out_xnor(out_xnor),
   .final_output(final_output),
   .in_wire(in_wire),
   .shift_out_wire(shift_out_wire));