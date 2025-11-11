// SVA for the provided design. Bind these checkers to the DUTs.

module full_adder_sva(input a, input b, input cin, input sum, input cout);
  // Sample on any input edge (combinational checker)
  localparam int unsigned W = 1;
  event fa_evt;
  // synthesizable event expression
  // Tools don't support 'event' assignments from expressions; inline the event in each assertion instead.

  // No X/Zs on relevant signals
  a_fa_no_x: assert property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin)
                              !($isunknown({a,b,cin,sum,cout})));

  // Functional truth table
  a_fa_sum:  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin)
                              sum == (a ^ b ^ cin));
  a_fa_cout: assert property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin)
                              cout == ((a & b) | (b & cin) | (a & cin)));

  // Coverage: all 8 input combinations observed
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b000);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b001);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b010);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b011);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b100);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b101);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b110);
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge cin or negedge cin) {a,b,cin}==3'b111);
endmodule


module gray_code_counter_sva(input clk, input reset, input [15:0] Q);
  default clocking cb @(posedge clk); endclocking

  // Async reset low forces and holds zero
  a_rst_edge:  assert property (@(negedge reset) Q==16'h0000);
  a_rst_hold:  assert property (!reset |-> (Q==16'h0000));

  // Next-state equation as coded
  a_next_eq:   assert property (reset && $past(reset) |-> Q == ($past(Q) ^ { $past(Q)[14:0], 1'b0 }));

  // Gray property (exactly one bit toggles per step when running)
  a_gray_step: assert property (reset && $past(reset) |-> $onehot(Q ^ $past(Q)));

  // Coverage: leaves zero and exercises each single-bit toggle
  c_leave_zero: cover property (reset && $past(reset) && (Q!=16'h0000));
  genvar i;
  generate for (i=0;i<16;i++) begin : C_TOG
    cover property (reset && $past(reset) && ((Q ^ $past(Q)) == (16'h1 << i)));
  end endgenerate
endmodule


module top_module_sva(input clk, input reset,
                      input a, input b, input cin,
                      input sum, input cout,
                      input [15:0] Q);
  default clocking cb @(posedge clk); endclocking

  // No X/Zs on top-level observable signals when out of reset
  a_top_no_x: assert property (reset |-> !($isunknown({a,b,cin,sum,cout,Q})) );

  // Connectivity/functional composition at top
  a_top_sum:  assert property (sum == (Q[0] ^ (a ^ b ^ cin)));
  a_top_cout: assert property (cout == ((a & b) | (b & cin) | (a & cin)));

  // Exercise XOR with Gray LSB
  c_q0_rose:  cover property (reset && $rose(Q[0]));
  c_q0_fell:  cover property (reset && $fell(Q[0]));
endmodule


// Bind checkers to DUTs
bind full_adder        full_adder_sva        fa_sva_inst       (.*);
bind gray_code_counter gray_code_counter_sva gcc_sva_inst      (.*);
bind top_module        top_module_sva        top_sva_inst      (.*);