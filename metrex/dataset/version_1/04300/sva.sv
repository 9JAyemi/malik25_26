// SVA for adder_with_carry
// Bind into the DUT to check internal wires and provide coverage
bind adder_with_carry adder_with_carry_sva sva();

module adder_with_carry_sva;

  // Access DUT signals directly (bound inside the module)
  // clk, reset, A, B, cin, sel, sum, cout
  // shifted_A, shifted_B, selected_input, temp_sum, temp_cout

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity: no X on inputs and outputs
  ap_no_x_in:  assert property (!$isunknown({A,B,cin,sel}));
  ap_no_x_out: assert property (!$isunknown({sum,cout}));

  // Barrel shifter behavior as implemented
  ap_shift_A_0: assert property ((sel==4'd0) |-> (shifted_A==A));
  ap_shift_B_0: assert property ((sel==4'd0) |-> (shifted_B==B));
  ap_shift_A_N: assert property ((sel!=4'd0) |-> (shifted_A==16'h0));
  ap_shift_B_N: assert property ((sel!=4'd0) |-> (shifted_B==16'h0));

  // Mux behavior as implemented
  ap_sel_in_0: assert property ((sel==4'd0) |-> (selected_input==shifted_A));
  ap_sel_in_N: assert property ((sel!=4'd0) |-> (selected_input==16'h0));

  // Full-adder internal relation
  ap_temp_add: assert property ({temp_cout,temp_sum} == {1'b0,shifted_A} + {1'b0,shifted_B} + cin);

  // Output relations
  ap_sum_eq:  assert property (sum  == (selected_input + temp_sum)); // 16-bit add, carry truncated
  ap_cout_eq: assert property (cout == temp_cout);

  // Consequences for sel != 0
  ap_selN_consistency: assert property ((sel!=4'd0) |-> (temp_sum=={15'b0,cin} && temp_cout==1'b0 && selected_input==16'h0 && sum=={15'b0,cin}));

  // End-to-end checks for sel == 0
  ap_sel0_sum:  assert property ((sel==4'd0) |-> (sum  == (A + (A + B + cin)[15:0])));
  ap_sel0_cout: assert property ((sel==4'd0) |-> (cout == (({1'b0,A} + {1'b0,B} + cin)[16])));

  // Combinational stability: if inputs hold, internals/outputs hold
  ap_stable: assert property ($stable({A,B,cin,sel}) |-> $stable({shifted_A,shifted_B,selected_input,temp_sum,temp_cout,sum,cout}));

  // Coverage
  // Cover all sel values and both cin values
  genvar i;
  generate
    for (i=0; i<16; i++) begin : C_SEL
      cp_sel:  cover property (sel==i);
      cp_sel_cin0: cover property (sel==i && cin==1'b0);
      cp_sel_cin1: cover property (sel==i && cin==1'b1);
    end
  endgenerate

  // Interesting scenarios
  cp_cout1_sel0: cover property (sel==4'd0 && cout==1'b1);
  cp_sum_zero_sel0: cover property (sel==4'd0 && sum==16'h0000);
  cp_sum_ffff_sel0: cover property (sel==4'd0 && sum==16'hFFFF);
  cp_reset_toggle: cover property ($rose(reset)) ; // observe reset activity
  cp_reset_deassert: cover property ($fell(reset));

endmodule