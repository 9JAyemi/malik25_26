// SVA for binary_adder: concise, high-quality checks + coverage
module binary_adder_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  S,
  input logic        Cout
);

  // Async reset drives zeros immediately (same timestep) and holds zeros while asserted
  ap_async_clear: assert property (@(negedge rst_n) ##0 (S==4'b0 && Cout==1'b0));
  ap_rst_hold   : assert property (@(posedge clk) !rst_n |-> (S==4'b0 && Cout==1'b0));

  // Registered adder correctness: outputs reflect previous-cycle inputs when out of reset
  ap_sum_correct: assert property (@(posedge clk)
                                   disable iff (!rst_n)
                                   $past(rst_n) |-> {Cout,S} == $past(A)+$past(B)+$past(Cin));

  // No X/Z on inputs or outputs when operating
  ap_no_x_inputs : assert property (@(posedge clk) disable iff (!rst_n) !$isunknown({A,B,Cin}));
  ap_no_x_outputs: assert property (@(posedge clk) disable iff (!rst_n) !$isunknown({S,Cout}));

  // Simple sanity: carry matches MSB of computed sum (redundant with ap_sum_correct, but precise)
  ap_cout_match: assert property (@(posedge clk)
                                  disable iff (!rst_n)
                                  $past(rst_n) |-> Cout == ( ($past(A)+$past(B)+$past(Cin)) >> 4 ));

  // Coverage: reset sequence, Cin values, carry/no-carry, and all S values 0..15
  cp_reset_release: cover property (@(posedge clk) !rst_n ##1 rst_n);
  cp_cin0: cover property (@(posedge clk) rst_n && $past(rst_n) && ($past(Cin)==1'b0));
  cp_cin1: cover property (@(posedge clk) rst_n && $past(rst_n) && ($past(Cin)==1'b1));
  cp_carry   : cover property (@(posedge clk) rst_n && $past(rst_n) && Cout);
  cp_nocarry : cover property (@(posedge clk) rst_n && $past(rst_n) && !Cout);

  genvar v;
  generate
    for (v=0; v<16; v++) begin: g_cov_S
      cover property (@(posedge clk) rst_n && $past(rst_n) && (S == v[3:0]));
    end
  endgenerate

endmodule

bind binary_adder binary_adder_sva sva_inst(.*);